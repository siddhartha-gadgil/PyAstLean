import numpy as np

def process_data(data, weights):
    try:
        # Calculate mean of the dataset
        m = np.mean(data)
        print(f"Dataset Global Mean: {m}")

        # Center the data by subtracting the mean
        # (Using a manual broadcast-like subtraction for this example)
        # Note: np.subtract is mapped to pyNumpySubtract
        centered = np.subtract(data, [[m, m], [m, m]])

        # Perform matrix multiplication
        # Note: np.matmul is mapped to pyNumpyMatmul
        result = np.matmul(centered, weights)
        return result
    except ValueError as e:
        print(f"Processing failed: {e}")
        # Fallback to a zero matrix if dimensions fail
        return np.zeros((2, 2))

def run_example():
    # Define a 2x2 dataset and a 2x2 weight matrix
    dataset = [
        [1.0, 2.0],
        [3.0, 4.0]
    ]
    weights = [
        [0.5, 0.5],
        [1.0, 2.0]
    ]

    print("=== PastaLean NumPy Showcase ===")
    print(f"Input Data: {dataset}")
    print(f"Weight Matrix: {weights}")

    # 1. Main Processing Pipeline
    print("\n[1] Running Data Pipeline:")
    output = process_data(dataset, weights)
    print(f"Final Result:\n{output}")

    # 2. Utility Operations
    print("\n[2] Structural Operations:")
    print(f"Identity Matrix (2x2):\n{np.eye(2)}")
    print(f"Flattened Weights: {np.ravel(weights)}")

    # 3. Shape Info
    # Note: np.shape returns (rows, cols)
    rows, cols = np.shape(dataset)
    print(f"Dataset Shape: {rows}x{cols}")

    # 4. Error Handling Simulation
    print("\n[3] Exception Handling (Mismatched Dimensions):")
    invalid_data = [[1.0, 2.0, 3.0]] # 1x3 matrix
    # This should trigger the ValueError in np.matmul(1x3, 2x2)
    process_data(invalid_data, weights)

if __name__ == "__main__":
    run_example()
