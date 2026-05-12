answer = 42

fruits = ["apple", "banana", "cherry"]
scores = {"math": 95, "science": 90}

def greet(name):
  return f"Hello, {name}!"

def calculate_sum():
    total = 0
    for i in range(10):
        total += i
    return total

if __name__ == "__main__":
    for _ in range(10):
        print(greet(1))
        calculate_sum()
