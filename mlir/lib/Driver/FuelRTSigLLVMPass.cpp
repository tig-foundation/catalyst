#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/InlineAsm.h"
#include <cstdlib>
#include <unordered_map>

using namespace llvm;

namespace {

// Custom function cost lookup table
static std::unordered_map<std::string, unsigned> createFunctionCostMap() {
    return {
        // Quantum gate operations - based on typical gate costs
        {"__catalyst__qis__Hadamard", 100},
        {"__catalyst__qis__PauliX", 50},
        {"__catalyst__qis__PauliY", 50}, 
        {"__catalyst__qis__PauliZ", 50},
        {"__catalyst__qis__RX", 75},
        {"__catalyst__qis__RY", 75},
        {"__catalyst__qis__RZ", 75},
        {"__catalyst__qis__CNOT", 150},
        {"__catalyst__qis__CZ", 150},
        {"__catalyst__qis__CY", 150},
        {"__catalyst__qis__SWAP", 200},
        {"__catalyst__qis__CSWAP", 300},
        {"__catalyst__qis__Toffoli", 400},
        {"__catalyst__qis__GlobalPhase", 25},
        
        // Measurement operations - typically expensive
        {"__catalyst__qis__Probs", 500},
        {"__catalyst__qis__Sample", 800},
        {"__catalyst__qis__Expval", 600},
        {"__catalyst__qis__Var", 700},
        {"__catalyst__qis__State", 1000},
        
        // Quantum runtime operations
        {"__catalyst__rt__qubit_allocate_array", 200},
        {"__catalyst__rt__qubit_release_array", 100},
        {"__catalyst__rt__array_get_element_ptr_1d", 10},
        {"__catalyst__rt__device_init", 1000},
        {"__catalyst__rt__device_release", 500},
        {"__catalyst__rt__initialize", 800},
        {"__catalyst__rt__finalize", 400},
        
        // Memory allocation operations  
        {"_mlir_memref_to_llvm_alloc", 150},
        {"malloc", 100},
        {"free", 50},
        {"calloc", 120},
        {"realloc", 80},
        
        // Math library functions
        {"sqrt", 15},
        {"sqrtf", 12},
        {"sin", 35},
        {"sinf", 30},
        {"cos", 35},
        {"cosf", 30},
        {"tan", 45},
        {"tanf", 40},
        {"exp", 35},
        {"expf", 30},
        {"log", 24},
        {"logf", 20},
        {"pow", 40},
        {"powf", 35},
        
        // String/IO operations
        {"printf", 200},
        {"fprintf", 220},
        {"sprintf", 180},
        {"puts", 100},
        {"memcpy", 30},
        {"memset", 20},
        {"strlen", 15},
        
        // Standard library
        {"exit", 1000},  // High cost since it's terminal
        {"abort", 1000},
    };
}

static const std::unordered_map<std::string, unsigned> FUNCTION_COSTS = createFunctionCostMap();

// Enhanced fuel cost calculation with function lookup
static unsigned getFuelCost(Instruction &I) {
    unsigned baseCost = 0;
    
    if (auto *Call = dyn_cast<CallInst>(&I)) {
        if (Function *Callee = Call->getCalledFunction()) {
            // Skip our own instrumentation functions
            if (Callee->getName() == "__check_fuel") {
                return 0;
            }
            
            // Check custom function cost table first
            std::string funcName = Callee->getName().str();
            auto it = FUNCTION_COSTS.find(funcName);
            if (it != FUNCTION_COSTS.end()) {
                errs() << "Custom cost for " << funcName << ": " << it->second << "\n";
                return it->second;
            }
            
            // Handle intrinsics
            if (Callee->isIntrinsic()) {
                if (Callee->getName().contains("sqrt")) return 15;
                if (Callee->getName().contains("sin") || Callee->getName().contains("cos")) return 35;
                if (Callee->getName().contains("exp")) return 35;
                if (Callee->getName().contains("log")) return 24;
                if (Callee->getName().contains("memcpy")) return 30;
                if (Callee->getName().contains("memset")) return 20;
                return 5; // Default intrinsic cost
            }
            
            // Default function call cost based on argument count
            unsigned argCost = std::min(8u, Call->arg_size());
            return 10 + argCost * 2; // Base cost + arg processing
        } else {
            // Indirect call - more expensive
            unsigned argCost = std::min(8u, Call->arg_size());
            return 20 + argCost * 3;
        }
    }
    
    // Regular instruction costs
    switch (I.getOpcode()) {
        case Instruction::Add:
        case Instruction::Sub:
        case Instruction::FAdd:
        case Instruction::FSub:
            baseCost = I.getType()->isFloatingPointTy() ? 5 : 1;
            break;
            
        case Instruction::Mul:
        case Instruction::FMul:
            baseCost = I.getType()->isFloatingPointTy() ? 7 : 3;
            break;
            
        case Instruction::UDiv:
        case Instruction::SDiv:
            baseCost = 12;
            break;
            
        case Instruction::FDiv:
            baseCost = 17;
            break;
            
        case Instruction::URem:
        case Instruction::SRem:
        case Instruction::FRem:
            baseCost = I.getType()->isFloatingPointTy() ? 20 : 15;
            break;
            
        case Instruction::Load:
            baseCost = 2;
            if (auto *LI = dyn_cast<LoadInst>(&I)) {
                if (LI->isVolatile()) baseCost *= 2;
            }
            break;
            
        case Instruction::Store:
            baseCost = 3;
            if (auto *SI = dyn_cast<StoreInst>(&I)) {
                if (SI->isVolatile()) baseCost *= 2;
            }
            break;
            
        case Instruction::Alloca:
            baseCost = 5; // Memory allocation
            break;
            
        case Instruction::GetElementPtr:
            baseCost = 1; // Address calculation
            break;
            
        case Instruction::ICmp:
            baseCost = 1;
            break;
            
        case Instruction::FCmp:
            baseCost = 3;
            break;
            
        case Instruction::Shl:
        case Instruction::LShr:
        case Instruction::AShr:
        case Instruction::And:
        case Instruction::Or:
        case Instruction::Xor:
            baseCost = 1;
            break;
            
        case Instruction::Select:
            baseCost = 3;
            break;
            
        case Instruction::InsertValue:
        case Instruction::ExtractValue:
            baseCost = 2;
            break;
            
        default:
            return 0; // No cost for other instructions
    }
    
    // Apply multipliers for vector types
    if (I.getType()->isVectorTy()) {
        baseCost *= 2;
    }
    
    return baseCost;
}

// Runtime signature prime calculation (simplified from FuelRTSig.cpp)
static uint64_t getInstructionPrime(const Instruction &I) {
    // Simplified prime mapping
    switch (I.getOpcode()) {
        case Instruction::Add:
            return I.getType()->isFloatingPointTy() ? 0x90B2AD995AF897CD : 0xEDC1A7F47ACD2EE3;
        case Instruction::Sub:
            return I.getType()->isFloatingPointTy() ? 0xC256B33A0EF0745F : 0x87353D33C2976737;
        case Instruction::Mul:
            return I.getType()->isFloatingPointTy() ? 0x9AF1495384190163 : 0x91C6A1D9B4EDC1AB;
        case Instruction::UDiv:
        case Instruction::SDiv:
            return 0xFD9B02FDC35C72B3;
        case Instruction::FDiv:
            return 0x966C40D3884717FF;
        case Instruction::Load:
            return 0x9A9E961B54B29955;
        case Instruction::Store:
            return 0x986CCCCFA9F5B10B;
        case Instruction::ICmp:
            return 0xB19319E767B773DF;
        case Instruction::FCmp:
            return 0xBF2A12007525FEED;
        case Instruction::Call:
            return 0x995e5c890782aab9;
        default:
            return 0x8374F43D807A6F91; // Default prime
    }
}

class FuelRTSigLLVMPass : public ModulePass {
public:
    static char ID;
    
    FuelRTSigLLVMPass() : ModulePass(ID) {}
    
    bool runOnModule(Module &M) override {
        errs() << "=== FUEL RTSIG LLVM PASS: Running on LLVM IR ===\n";
        
        // Get environment variables
        const char *instrumentFuelStr = std::getenv("INSTRUMENT_FUEL");
        bool instrumentFuel = instrumentFuelStr ? std::atoi(instrumentFuelStr) : true;
        
        const char *instrumentRTSigStr = std::getenv("INSTRUMENT_RTSIG");
        bool instrumentRTSig = instrumentRTSigStr ? std::atoi(instrumentRTSigStr) : true;
        
        // Create global variables
        createGlobalVariables(M);
        
        // Create helper functions
        createHelperFunctions(M);
        
        // Instrument all functions
        for (Function &F : M) {
            if (!F.isDeclaration() && 
                !F.getName().starts_with("__fuel_") && 
                !F.getName().starts_with("__check_") &&
                !F.getName().starts_with("llvm.")) {
                instrumentFunction(F, instrumentFuel, instrumentRTSig);
            }
        }
        
        errs() << "=== FUEL RTSIG LLVM PASS: Completed ===\n";
        return true; // Module was modified
    }

private:
    GlobalVariable *fuelGlobal = nullptr;
    GlobalVariable *runtimeSigGlobal = nullptr;
    Function *checkFuelFunc = nullptr;
    
    void createGlobalVariables(Module &M) {
        LLVMContext &Ctx = M.getContext();
        
        const char* fuelStr = std::getenv("FUEL");
        unsigned fuel = fuelStr ? std::atoi(fuelStr) : 10000;
        
        // Create global fuel counter
        fuelGlobal = new GlobalVariable(
            M,
            Type::getInt64Ty(Ctx),
            false, // not constant
            GlobalValue::ExternalLinkage,
            ConstantInt::get(Type::getInt64Ty(Ctx), fuel),
            "__fuel_remaining"
        );
        
        // Create global runtime signature
        runtimeSigGlobal = new GlobalVariable(
            M,
            Type::getInt64Ty(Ctx),
            false, // not constant
            GlobalValue::ExternalLinkage,
            ConstantInt::get(Type::getInt64Ty(Ctx), 0x4C4C4D564F4C4C4C),
            "__runtime_signature"
        );
        
        errs() << "Created global variables\n";
    }
    
    void createHelperFunctions(Module &M) {
        LLVMContext &Ctx = M.getContext();
        
        // Create check fuel function
        FunctionType *CheckFuelType = FunctionType::get(
            Type::getVoidTy(Ctx),
            {Type::getInt64Ty(Ctx)},
            false
        );
        
        checkFuelFunc = Function::Create(
            CheckFuelType,
            GlobalValue::ExternalLinkage,
            "__check_fuel",
            M
        );
        
        // Implement the check fuel function
        BasicBlock *EntryBB = BasicBlock::Create(Ctx, "entry", checkFuelFunc);
        BasicBlock *ExitBB = BasicBlock::Create(Ctx, "exit", checkFuelFunc);
        BasicBlock *ContinueBB = BasicBlock::Create(Ctx, "continue", checkFuelFunc);
        
        IRBuilder<> Builder(EntryBB);
        
        Value *FuelArg = checkFuelFunc->getArg(0);
        Value *CurrentFuel = Builder.CreateLoad(Type::getInt64Ty(Ctx), fuelGlobal);
        Value *NewFuel = Builder.CreateSub(CurrentFuel, FuelArg);
        Builder.CreateStore(NewFuel, fuelGlobal);
        
        Value *ShouldAbort = Builder.CreateICmpSLT(
            NewFuel,
            ConstantInt::get(Type::getInt64Ty(Ctx), 0)
        );
        
        Builder.CreateCondBr(ShouldAbort, ExitBB, ContinueBB);
        
        // Exit block - just return for now  
        Builder.SetInsertPoint(ExitBB);
        
        // Simple placeholder - just load the runtime signature and discard it
        Value *RuntimeSig = Builder.CreateLoad(Type::getInt64Ty(Ctx), runtimeSigGlobal);
        // Use the value to avoid unused variable warning
        Builder.CreateStore(RuntimeSig, runtimeSigGlobal);
        
        // Return normally for now
        Builder.CreateRetVoid();
        
        // Continue block
        Builder.SetInsertPoint(ContinueBB);
        Builder.CreateRetVoid();
        
        errs() << "Created helper functions\n";
    }
    
    void instrumentFunction(Function &F, bool instrumentFuel, bool instrumentRTSig) {
        errs() << "Instrumenting function: " << F.getName() << "\n";
        
        // Instrument each basic block
        for (BasicBlock &BB : F) {
            instrumentBasicBlock(BB, instrumentFuel, instrumentRTSig);
        }
    }
    
    void instrumentBasicBlock(BasicBlock &BB, bool instrumentFuel, bool instrumentRTSig) {
        LLVMContext &Ctx = BB.getContext();
        
        unsigned totalFuelCost = 0;
        uint64_t blockSignature = 0;
        
        // Calculate costs and signatures for all instructions in this block
        for (Instruction &I : BB) {
            if (instrumentFuel) {
                unsigned cost = getFuelCost(I);
                totalFuelCost += cost;
            }
            
            if (instrumentRTSig) {
                uint64_t prime = getInstructionPrime(I);
                if (prime != 0) {
                    // Simple position-based modification
                    uint64_t position = std::distance(BB.begin(), BasicBlock::iterator(I));
                    blockSignature ^= (prime + position * 0x123456789ABCDEF);
                }
            }
        }
        
        // Insert instrumentation at the beginning of the block
        if ((instrumentFuel && totalFuelCost > 0) || (instrumentRTSig && blockSignature != 0)) {
            IRBuilder<> Builder(&BB, BB.begin());
            
            if (instrumentFuel && totalFuelCost > 0) {
                Value *FuelCost = ConstantInt::get(Type::getInt64Ty(Ctx), totalFuelCost);
                Builder.CreateCall(checkFuelFunc, {FuelCost});
            }
            
            if (instrumentRTSig && blockSignature != 0) {
                Value *CurrentSig = Builder.CreateLoad(Type::getInt64Ty(Ctx), runtimeSigGlobal);
                Value *SigValue = ConstantInt::get(Type::getInt64Ty(Ctx), blockSignature);
                Value *NewSig = Builder.CreateXor(CurrentSig, SigValue);
                Builder.CreateStore(NewSig, runtimeSigGlobal);
            }
        }
    }
};

char FuelRTSigLLVMPass::ID = 0;

} // anonymous namespace

// Make the pass available to the driver
ModulePass *createFuelRTSigLLVMPass() {
    return new FuelRTSigLLVMPass();
}