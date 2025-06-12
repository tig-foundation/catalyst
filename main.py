from catalyst import qjit
from catalyst.debug import get_compilation_stage
import pennylane as qml
import numpy as np

# Your existing functions...
def equal_superposition(wires):
    for wire in wires:
        qml.Hadamard(wires=wire)

def oracle(wires, omega):
    qml.FlipSign(omega, wires=wires)

def num_grover_iterations(N, M):
    return np.ceil(np.sqrt(N / M) * np.pi / 4).astype(int)

def grover_circuit(num_qubits):
    wires = list(range(num_qubits))
    omega = np.array([np.zeros(num_qubits), np.ones(num_qubits)])
    M = len(omega)
    N = 2**num_qubits

    equal_superposition(wires)

    for _ in range(num_grover_iterations(N, M)):
        for omg in omega:
            oracle(wires, omg)
        qml.templates.GroverOperator(wires)

    return qml.probs(wires=wires)

NUM_QUBITS = 4  # Reduced for cleaner output

dev = qml.device("lightning.qubit", wires=NUM_QUBITS)

@qjit(keep_intermediate=True)  # Enable debug output
@qml.qnode(dev)
def circuit_qjit():
    return grover_circuit(NUM_QUBITS)

# Compile and run
results = circuit_qjit()

# Output MLIR representations
print("=== Initial MLIR ===")
print(circuit_qjit.mlir)

print("\n=== After Quantum Compilation ===")
print(get_compilation_stage(circuit_qjit, "QuantumCompilationPass"))

print("\n=== LLVM IR ===")
llvm_ir = get_compilation_stage(circuit_qjit, "llvm_ir")

# Save LLVM IR to file
with open('circuit.ll', 'w') as f:
    f.write(llvm_ir)

print("LLVM IR saved to circuit.ll")