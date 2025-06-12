// Copyright 2024 Xanadu Quantum Technologies Inc.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at

//     http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#define DEBUG_TYPE "fuelrtsig"

#include "llvm/Support/Debug.h"

#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/LLVMIR/LLVMDialect.h"
#include "mlir/Dialect/MemRef/IR/MemRef.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/Pass/Pass.h"
#include "mlir/Transforms/DialectConversion.h"
#include "mlir/Transforms/GreedyPatternRewriteDriver.h"

#include "Catalyst/Transforms/Passes.h"

#include <cstdlib>  // For getenv

using namespace mlir;

namespace catalyst {

#define GEN_PASS_DEF_FUELRTSIGPASS
#include "Catalyst/Transforms/Passes.h.inc"

struct FuelCosts {
    // Basic operation costs
    static constexpr unsigned Add = 1;
    static constexpr unsigned Mul = 3;
    static constexpr unsigned Div = 12;
    static constexpr unsigned FAdd = 5;
    static constexpr unsigned FMul = 7;
    static constexpr unsigned FDiv = 17;
    static constexpr unsigned Load = 2;
    static constexpr unsigned Store = 3;
    static constexpr unsigned Call = 5;
    
    // Quantum operation costs
    static constexpr unsigned QuantumGate = 10;
    static constexpr unsigned QuantumAlloc = 5;
    static constexpr unsigned QuantumExtract = 2;
    static constexpr unsigned QuantumMeasurement = 20;
    static constexpr unsigned QuantumDefault = 3;
};

struct InstructionPrimes {
    // Simplified set of primes for MLIR operations
    static constexpr uint64_t Add_i32 = 0xEDC1A7F47ACD2EE3;
    static constexpr uint64_t Mul_i32 = 0x91C6A1D9B4EDC1AB;
    static constexpr uint64_t Div_i32 = 0xFD9B02FDC35C72B3;
    static constexpr uint64_t Add_f32 = 0x90B2AD995AF897CD;
    static constexpr uint64_t Mul_f32 = 0x9AF1495384190163;
    static constexpr uint64_t Div_f32 = 0x966C40D3884717FF;
    static constexpr uint64_t Load_op = 0x9A9E961B54B29955;
    static constexpr uint64_t Store_op = 0x986CCCCFA9F5B10B;
    static constexpr uint64_t Call_op = 0x995e5c890782aab9;
};

class FuelRTSigPass : public catalyst::impl::FuelRTSigPassBase<FuelRTSigPass> {
public:
    void runOnOperation() override;

private:
    unsigned getFuelCost(Operation *op);
    uint64_t getRuntimeSignature(Operation *op);
    void instrumentFunction(func::FuncOp funcOp);
    void createGlobalVariables(ModuleOp moduleOp);
    func::FuncOp createCheckFuelFunction(ModuleOp moduleOp);
    func::FuncOp createCommitTlsFunction(ModuleOp moduleOp);
    
    // Global variables for fuel and runtime signature tracking
    LLVM::GlobalOp debugMarkerGlobal;
    LLVM::GlobalOp fuelGlobal;
    LLVM::GlobalOp runtimeSigGlobal;
    LLVM::GlobalOp threadLocalFuelGlobal;
    LLVM::GlobalOp threadLocalRuntimeSigGlobal;
    
    // Helper functions - keep as func::FuncOp
    func::FuncOp checkFuelFunc;
    func::FuncOp commitTlsFunc;
};

unsigned FuelRTSigPass::getFuelCost(Operation *op)
{
    // Existing arithmetic operations
    if (isa<arith::AddIOp, arith::SubIOp>(op)) {
        return FuelCosts::Add;
    }
    if (isa<arith::MulIOp>(op)) {
        return FuelCosts::Mul;
    }
    if (isa<arith::DivSIOp, arith::DivUIOp>(op)) {
        return FuelCosts::Div;
    }
    if (isa<arith::AddFOp, arith::SubFOp>(op)) {
        return FuelCosts::FAdd;
    }
    if (isa<arith::MulFOp>(op)) {
        return FuelCosts::FMul;
    }
    if (isa<arith::DivFOp>(op)) {
        return FuelCosts::FDiv;
    }
    if (isa<memref::LoadOp>(op)) {
        return FuelCosts::Load;
    }
    if (isa<memref::StoreOp>(op)) {
        return FuelCosts::Store;
    }
    if (isa<func::CallOp>(op)) {
        return FuelCosts::Call;
    }
    
    // Add quantum operations
    if (op->getName().getStringRef().starts_with("quantum.")) {
        if (op->getName().getStringRef() == "quantum.custom") {
            return 10; // Cost for quantum gates
        }
        if (op->getName().getStringRef() == "quantum.alloc") {
            return 5;  // Cost for qubit allocation
        }
        if (op->getName().getStringRef() == "quantum.extract") {
            return 2;  // Cost for qubit extraction
        }
        if (op->getName().getStringRef() == "quantum.insert") {
            return 2;  // Cost for qubit insertion
        }
        if (op->getName().getStringRef() == "quantum.probs") {
            return 20; // Cost for probability measurement
        }
        return 3; // Default cost for other quantum operations
    }
    
    return 0;
}

uint64_t FuelRTSigPass::getRuntimeSignature(Operation *op)
{
    // Existing arithmetic operations  
    if (isa<arith::AddIOp, arith::SubIOp>(op)) {
        return InstructionPrimes::Add_i32;
    }
    if (isa<arith::MulIOp>(op)) {
        return InstructionPrimes::Mul_i32;
    }
    if (isa<arith::DivSIOp, arith::DivUIOp>(op)) {
        return InstructionPrimes::Div_i32;
    }
    if (isa<arith::AddFOp, arith::SubFOp>(op)) {
        return InstructionPrimes::Add_f32;
    }
    if (isa<arith::MulFOp>(op)) {
        return InstructionPrimes::Mul_f32;
    }
    if (isa<arith::DivFOp>(op)) {
        return InstructionPrimes::Div_f32;
    }
    if (isa<memref::LoadOp>(op)) {
        return InstructionPrimes::Load_op;
    }
    if (isa<memref::StoreOp>(op)) {
        return InstructionPrimes::Store_op;
    }
    if (isa<func::CallOp>(op)) {
        return InstructionPrimes::Call_op;
    }
    
    // Add quantum operation signatures
    if (op->getName().getStringRef().starts_with("quantum.")) {
        if (op->getName().getStringRef() == "quantum.custom") {
            return 0x9A5B8C3D2E1F4A6B; // Unique prime for quantum gates
        }
        if (op->getName().getStringRef() == "quantum.alloc") {
            return 0x8E4F1A2B9C5D3F7E; // Unique prime for alloc
        }
        if (op->getName().getStringRef() == "quantum.extract") {
            return 0x7D3C9A1B4E8F2C5A; // Unique prime for extract
        }
        if (op->getName().getStringRef() == "quantum.probs") {
            return 0x6C2B8A9D1E4F7B3C; // Unique prime for measurements
        }
        return 0x5A1B7C8D9E2F4A6B; // Default quantum operation signature
    }
    
    return 0;
}

void FuelRTSigPass::createGlobalVariables(ModuleOp moduleOp)
{
    OpBuilder builder(moduleOp.getContext());
    builder.setInsertionPointToStart(moduleOp.getBody());
    
    auto i64Type = builder.getI64Type();
    
    // Add a debug marker global that's easy to spot
    debugMarkerGlobal = builder.create<LLVM::GlobalOp>(
        builder.getUnknownLoc(),
        i64Type,
        /*isConstant=*/true,
        LLVM::Linkage::External,
        "__FUEL_RTSIG_PASS_WAS_HERE_DEBUG_MARKER",
        builder.getI64IntegerAttr(0xDEADBEEFCAFEBABE)
    );
    
    // Create global fuel variable
    fuelGlobal = builder.create<LLVM::GlobalOp>(
        builder.getUnknownLoc(),
        i64Type,
        /*isConstant=*/false,
        LLVM::Linkage::External,
        "__fuel_remaining",
        builder.getI64IntegerAttr(10000)
    );
    
    // Create global runtime signature variable
    runtimeSigGlobal = builder.create<LLVM::GlobalOp>(
        builder.getUnknownLoc(),
        i64Type,
        /*isConstant=*/false,
        LLVM::Linkage::External,
        "__runtime_signature",
        builder.getI64IntegerAttr(0x4C4C4D564F4C4C4C)
    );
    
    // Create thread-local fuel variable
    threadLocalFuelGlobal = builder.create<LLVM::GlobalOp>(
        builder.getUnknownLoc(),
        i64Type,
        /*isConstant=*/false,
        LLVM::Linkage::External,
        "__thread_local_fuel_used",
        builder.getI64IntegerAttr(0)
    );
    threadLocalFuelGlobal->setAttr("thread_local", builder.getUnitAttr());
    
    // Create thread-local runtime signature variable
    threadLocalRuntimeSigGlobal = builder.create<LLVM::GlobalOp>(
        builder.getUnknownLoc(),
        i64Type,
        /*isConstant=*/false,
        LLVM::Linkage::External,
        "__thread_local_runtime_signature",
        builder.getI64IntegerAttr(0)
    );
    threadLocalRuntimeSigGlobal->setAttr("thread_local", builder.getUnitAttr());
}

func::FuncOp FuelRTSigPass::createCheckFuelFunction(ModuleOp moduleOp)
{
    OpBuilder builder(moduleOp.getContext());
    builder.setInsertionPointToEnd(moduleOp.getBody());
    
    auto i64Type = builder.getI64Type();
    
    // Create function type: void __check_fuel(i64)
    auto funcType = builder.getFunctionType({i64Type}, {});
    
    auto checkFuelFunc = builder.create<func::FuncOp>(
        builder.getUnknownLoc(),
        "__check_fuel",
        funcType
    );
    checkFuelFunc.setPrivate();
    
    // Create function body
    Block *entryBlock = checkFuelFunc.addEntryBlock();
    builder.setInsertionPointToStart(entryBlock);
    
    Value fuelArg = entryBlock->getArgument(0);
    
    // Atomic subtract: current_fuel = atomic_sub(fuel_global, fuel_arg)
    auto fuelGlobalAddr = builder.create<LLVM::AddressOfOp>(
        builder.getUnknownLoc(),
        LLVM::LLVMPointerType::get(builder.getContext()),
        fuelGlobal.getSymName()
    );
    
    auto currentFuel = builder.create<LLVM::AtomicRMWOp>(
        builder.getUnknownLoc(),
        LLVM::AtomicBinOp::sub,
        fuelGlobalAddr,
        fuelArg,
        LLVM::AtomicOrdering::monotonic
    );
    
    // Check if (current_fuel - fuel_arg) < 0
    auto newFuel = builder.create<arith::SubIOp>(
        builder.getUnknownLoc(),
        currentFuel,
        fuelArg
    );
    
    auto zero = builder.create<LLVM::ConstantOp>(
        builder.getUnknownLoc(), builder.getI64IntegerAttr(0));
    
    auto shouldAbort = builder.create<arith::CmpIOp>(
        builder.getUnknownLoc(),
        arith::CmpIPredicate::slt,
        newFuel,
        zero
    );
    
    // Use scf.if for conditional execution
    builder.create<scf::IfOp>(
        builder.getUnknownLoc(),
        shouldAbort,
        [&](OpBuilder &b, Location loc) {
            // Load runtime signature
            auto runtimeSigAddr = b.create<LLVM::AddressOfOp>(
                loc,
                LLVM::LLVMPointerType::get(b.getContext()),
                runtimeSigGlobal.getSymName()
            );
            
            b.create<LLVM::LoadOp>(
                loc,
                i64Type,
                runtimeSigAddr
            );
            
            // For now, just return - you could add printf functionality here
            b.create<scf::YieldOp>(loc);
        }
    );
    
    builder.create<func::ReturnOp>(builder.getUnknownLoc());
    
    return checkFuelFunc;
}

func::FuncOp FuelRTSigPass::createCommitTlsFunction(ModuleOp moduleOp)
{
    OpBuilder builder(moduleOp.getContext());
    builder.setInsertionPointToEnd(moduleOp.getBody());
    
    auto i64Type = builder.getI64Type();
    
    // Create function type: void __commit_tls()
    auto funcType = builder.getFunctionType({}, {});
    
    auto commitTlsFunc = builder.create<func::FuncOp>(
        builder.getUnknownLoc(),
        "__commit_tls",
        funcType
    );
    commitTlsFunc.setPrivate();
    
    // Create function body
    Block *entryBlock = commitTlsFunc.addEntryBlock();
    builder.setInsertionPointToStart(entryBlock);
    
    // Load thread-local fuel used
    auto threadFuelAddr = builder.create<LLVM::AddressOfOp>(
        builder.getUnknownLoc(),
        LLVM::LLVMPointerType::get(builder.getContext()),
        threadLocalFuelGlobal.getSymName()
    );
    
    auto threadFuelUsed = builder.create<LLVM::LoadOp>(
        builder.getUnknownLoc(),
        i64Type,
        threadFuelAddr
    );
    
    // Check if fuel used > 0
    auto zero = builder.create<LLVM::ConstantOp>(
        builder.getUnknownLoc(), builder.getI64IntegerAttr(0));
    
    auto hasFuelUsed = builder.create<arith::CmpIOp>(
        builder.getUnknownLoc(),
        arith::CmpIPredicate::sgt,
        threadFuelUsed,
        zero
    );
    
    builder.create<scf::IfOp>(
        builder.getUnknownLoc(),
        hasFuelUsed,
        [&](OpBuilder &b, Location loc) {
            // Call __check_fuel with thread fuel used
            auto checkFuelSymbol = SymbolRefAttr::get(b.getContext(), "__check_fuel");
            b.create<func::CallOp>(loc, checkFuelSymbol, TypeRange{}, ValueRange{threadFuelUsed});
            
            // Reset thread-local fuel to 0
            auto zeroLocal = b.create<LLVM::ConstantOp>(loc, b.getI64IntegerAttr(0));
            b.create<LLVM::StoreOp>(loc, zeroLocal, threadFuelAddr);
            b.create<scf::YieldOp>(loc);
        }
    );
    
    // Handle runtime signature
    auto threadSigAddr = builder.create<LLVM::AddressOfOp>(
        builder.getUnknownLoc(),
        LLVM::LLVMPointerType::get(builder.getContext()),
        threadLocalRuntimeSigGlobal.getSymName()
    );
    
    auto threadSig = builder.create<LLVM::LoadOp>(
        builder.getUnknownLoc(),
        i64Type,
        threadSigAddr
    );
    
    // Check if signature != 0
    auto hasSig = builder.create<arith::CmpIOp>(
        builder.getUnknownLoc(),
        arith::CmpIPredicate::ne,
        threadSig,
        zero
    );
    
    builder.create<scf::IfOp>(
        builder.getUnknownLoc(),
        hasSig,
        [&](OpBuilder &b, Location loc) {
            // Atomic XOR with global runtime signature
            auto runtimeSigAddr = b.create<LLVM::AddressOfOp>(
                loc,
                LLVM::LLVMPointerType::get(builder.getContext()),
                runtimeSigGlobal.getSymName()
            );
            
            b.create<LLVM::AtomicRMWOp>(
                loc,
                LLVM::AtomicBinOp::_xor,
                runtimeSigAddr,
                threadSig,
                LLVM::AtomicOrdering::monotonic
            );
            
            // Reset thread-local signature to 0
            auto zeroLocal = b.create<LLVM::ConstantOp>(loc, b.getI64IntegerAttr(0));
            b.create<LLVM::StoreOp>(loc, zeroLocal, threadSigAddr);
            b.create<scf::YieldOp>(loc);
        }
    );
    
    builder.create<func::ReturnOp>(builder.getUnknownLoc());
    
    return commitTlsFunc;
}

void FuelRTSigPass::instrumentFunction(func::FuncOp funcOp)
{
    ModuleOp funcModule = funcOp->getParentOfType<ModuleOp>();
    ModuleOp topModule = getOperation();
    OpBuilder builder(funcOp.getContext());

    if (funcModule != topModule) {
        OpBuilder b(funcModule.getContext());
        b.setInsertionPointToStart(funcModule.getBody());

        auto declareGlobal = [&](LLVM::GlobalOp global, bool isThreadLocal) {
            if (global && !funcModule.lookupSymbol(global.getSymName())) {
                auto newGlobal = b.create<LLVM::GlobalOp>(global.getLoc(), global.getType(),
                                                          global.getConstant(),
                                                          LLVM::Linkage::External,
                                                          global.getSymName(), nullptr);
                if (isThreadLocal) {
                    newGlobal->setAttr("thread_local", b.getUnitAttr());
                }
            }
        };

        declareGlobal(debugMarkerGlobal, false);
        declareGlobal(fuelGlobal, false);
        declareGlobal(runtimeSigGlobal, false);
        declareGlobal(threadLocalFuelGlobal, true);
        declareGlobal(threadLocalRuntimeSigGlobal, true);

        auto declareFunc = [&](func::FuncOp fn) {
            if (fn && !funcModule.lookupSymbol(fn.getName())) {
                auto newFunc = b.create<func::FuncOp>(fn.getLoc(), fn.getName(), fn.getFunctionType());
                newFunc.setPrivate();
            }
        };
        declareFunc(checkFuelFunc);
        declareFunc(commitTlsFunc);
    }

    // Add a debug marker at the beginning of every function
    Block &entryBlock = funcOp.getBlocks().front();
    builder.setInsertionPointToStart(&entryBlock);
    
    // Create a dummy computation that won't get optimized away
    auto i64Type = builder.getI64Type();
    auto magicNumber = builder.create<LLVM::ConstantOp>(
        builder.getUnknownLoc(), builder.getI64IntegerAttr(0x123456789ABCDEF0));
    
    auto anotherNumber = builder.create<LLVM::ConstantOp>(
        builder.getUnknownLoc(), builder.getI64IntegerAttr(1));
    
    // Do an add that creates a recognizable pattern
    auto debugResult = builder.create<arith::AddIOp>(
        builder.getUnknownLoc(), magicNumber, anotherNumber);
    
    // Store it to a dummy global to prevent optimization
    auto debugAddr = builder.create<LLVM::AddressOfOp>(
        builder.getUnknownLoc(), LLVM::LLVMPointerType::get(builder.getContext()),
        debugMarkerGlobal.getSymName());
    
    builder.create<LLVM::StoreOp>(builder.getUnknownLoc(), debugResult, debugAddr);
    
    // Walk through all blocks in the function
    funcOp.walk([&](Block *block) {
        unsigned blockFuelCost = 0;
        uint64_t blockRuntimeSig = 0;
        
        // Calculate total fuel cost and runtime signature for the block
        for (Operation &op : *block) {
            blockFuelCost += getFuelCost(&op);
            blockRuntimeSig ^= getRuntimeSignature(&op);
        }
        
        if (blockFuelCost > 0 || blockRuntimeSig != 0) {
            // Insert instrumentation at the beginning of the block
            builder.setInsertionPointToStart(block);
            
            if (blockFuelCost > 0) {
                // Add fuel cost to thread-local counter
                auto fuelConstant = builder.create<LLVM::ConstantOp>(
                    builder.getUnknownLoc(),
                    builder.getI64IntegerAttr(blockFuelCost)
                );
                
                // Load current thread-local fuel
                auto threadFuelAddr = builder.create<LLVM::AddressOfOp>(
                    builder.getUnknownLoc(),
                    LLVM::LLVMPointerType::get(builder.getContext()),
                    threadLocalFuelGlobal.getSymName()
                );
                
                auto currentFuel = builder.create<LLVM::LoadOp>(
                    builder.getUnknownLoc(),
                    i64Type,
                    threadFuelAddr
                );
                
                // Add to current fuel
                auto newFuel = builder.create<arith::AddIOp>(
                    builder.getUnknownLoc(),
                    currentFuel,
                    fuelConstant
                );
                
                // Store back to thread-local fuel
                builder.create<LLVM::StoreOp>(
                    builder.getUnknownLoc(),
                    newFuel,
                    threadFuelAddr
                );
            }
            
            if (blockRuntimeSig != 0) {
                // Update thread-local runtime signature
                auto sigConstant = builder.create<LLVM::ConstantOp>(
                    builder.getUnknownLoc(),
                    builder.getI64IntegerAttr(blockRuntimeSig)
                );
                
                // Load current thread-local signature
                auto threadSigAddr = builder.create<LLVM::AddressOfOp>(
                    builder.getUnknownLoc(),
                    LLVM::LLVMPointerType::get(builder.getContext()),
                    threadLocalRuntimeSigGlobal.getSymName()
                );
                
                auto currentSig = builder.create<LLVM::LoadOp>(
                    builder.getUnknownLoc(),
                    i64Type,
                    threadSigAddr
                );
                
                // XOR with new signature
                auto newSig = builder.create<arith::XOrIOp>(
                    builder.getUnknownLoc(),
                    currentSig,
                    sigConstant
                );
                
                // Store back to thread-local signature
                builder.create<LLVM::StoreOp>(
                    builder.getUnknownLoc(),
                    newSig,
                    threadSigAddr
                );
            }
        }
    });
    
    // Add commit calls at function exit points - use func::CallOp
    funcOp.walk([&](func::ReturnOp returnOp) {
        builder.setInsertionPoint(returnOp);
        auto commitSymbol = SymbolRefAttr::get(builder.getContext(), "__commit_tls");
        builder.create<func::CallOp>(
            builder.getUnknownLoc(),
            commitSymbol,
            TypeRange{},
            ValueRange{}
        );
    });
}

void FuelRTSigPass::runOnOperation()
{
    // Add unconditional debug output that will always print
    llvm::errs() << "=== FUELRTSIGPASS: PASS IS DEFINITELY RUNNING ===\n";
    llvm::errs().flush();
    
    LLVM_DEBUG(llvm::dbgs() << "FuelRTSigPass: Starting pass execution\n");
    
    // Check for environment variable to trigger segfault for debugging
    if (const char *crashEnv = std::getenv("FUEL_RTSIG_CRASH")) {
        if (crashEnv && std::string(crashEnv) == "1") {
            llvm::errs() << "=== FUELRTSIGPASS: CRASHING AS REQUESTED ===\n";
            llvm::errs().flush();
            LLVM_DEBUG(llvm::dbgs() << "FuelRTSigPass: FUEL_RTSIG_CRASH=1 detected, triggering segfault\n");
            
            volatile int *nullPtr = nullptr;
            *nullPtr = 42;  // This will segfault
        }
    }
    
    ModuleOp moduleOp = getOperation();
    
    llvm::errs() << "=== FUELRTSIGPASS: Creating globals and functions ===\n";
    llvm::errs().flush();
    
    LLVM_DEBUG(llvm::dbgs() << "FuelRTSigPass: Creating global variables\n");
    createGlobalVariables(moduleOp);
    
    LLVM_DEBUG(llvm::dbgs() << "FuelRTSigPass: Creating helper functions\n");
    checkFuelFunc = createCheckFuelFunction(moduleOp);
    commitTlsFunc = createCommitTlsFunction(moduleOp);
    
    // Count functions to instrument
    int functionCount = 0;
    moduleOp.walk([&](func::FuncOp funcOp) {
        if (funcOp.isDeclaration()) {
            return;
        }
        if (funcOp.getName().starts_with("__check_fuel") ||
            funcOp.getName().starts_with("__commit_tls")) {
            return;
        }
        functionCount++;
        llvm::errs() << "=== FUELRTSIGPASS: Instrumenting function: " << funcOp.getName() << " ===\n";
        llvm::errs().flush();
        LLVM_DEBUG(llvm::dbgs() << "FuelRTSigPass: Instrumenting function: " << funcOp.getName() << "\n");
        instrumentFunction(funcOp);
    });
    
    llvm::errs() << "=== FUELRTSIGPASS: Instrumented " << functionCount << " functions ===\n";
    llvm::errs().flush();
    LLVM_DEBUG(llvm::dbgs() << "FuelRTSigPass: Instrumented " << functionCount << " functions\n");
}

std::unique_ptr<Pass> createFuelRTSigPass()
{
    return std::make_unique<FuelRTSigPass>();
}

} // namespace catalyst 
