import tkinter as tk  # Importing the tkinter module for GUI
import z3  # Importing the Z3 solver library
from itertools import chain  # Importing chain function from itertools

class SudokuSolverApp:
    def __init__(self, master):
        self.master = master
        master.title("Sudoku Solver")  # Setting the title of the GUI window

        # Initializing a 9x9 grid of StringVar objects to hold the values of Sudoku grid cells
        self.sudoku_grid = [[tk.StringVar(master, '0') for _ in range(9)] for _ in range(9)]

        self.create_widgets()  # Calling the method to create GUI widgets

    def create_widgets(self):
        # Creating Entry widgets for each cell in the Sudoku grid
        for i in range(9):
            for j in range(9):
                entry = tk.Entry(self.master, width=2, textvariable=self.sudoku_grid[i][j],
                                 justify="center", font=("Arial", 16))  # Configuring Entry widget properties
                entry.grid(row=i, column=j)  # Placing the Entry widget in the grid
                if (i // 3 + j // 3) % 2 == 0:
                    entry.configure(bg="#f0f0f0")  # Light gray background for alternate cells
                else:
                    entry.configure(bg="#ffffff")  # White background for alternate cells
        
        # Creating a Solve button to initiate Sudoku puzzle solving
        solve_button = tk.Button(self.master, text="Solve", command=self.solve_sudoku,
                                 bg="#4CAF50", fg="white")  # Configuring button properties
        solve_button.grid(row=9, column=4, pady=20)  # Placing the button in the grid

    def solve_sudoku(self):
        # Creating a 9x9 array of Z3 integer variables to represent the Sudoku grid
        x = [[z3.Int(f'x_{i}_{j}') for i in range(9)] for j in range(9)]
        
        # Defining range constraints for Z3 variables (values between 1 and 9)
        range_c = [z3.And(i >= 1, i <= 9) for i in chain.from_iterable(x)]

        # Creating constraints based on the initial Sudoku grid values
        instance = [[int(var.get()) for var in row] for row in self.sudoku_grid]
        instance_c = [z3.If(instance[i][j] == 0, True, instance[i][j] == x[i][j])
                      for i in range(9) for j in range(9)]

        # Creating constraints to ensure uniqueness in rows, columns, and squares
        row_c = [z3.Distinct(i) for i in x]
        column_c = [z3.Distinct(list(chain.from_iterable(x))[i::9]) for i in range(9)]
        square_c = [z3.Distinct([x[j + l][i + k] for l in range(3) for k in range(3)])
                    for j in range(0, 9, 3) for i in range(0, 9, 3)]

        # Combining all constraints into a single list
        sudoku_c = range_c + instance_c + row_c + column_c + square_c

        # Creating a Z3 solver object and adding constraints
        solver = z3.Solver()
        solver.add(sudoku_c)

        # Checking for satisfiability of constraints and solving the Sudoku puzzle
        if solver.check() == z3.sat:
            m = solver.model()  # Getting the model containing the solution
            # Updating the GUI grid with the solved Sudoku values
            for i in range(9):
                for j in range(9):
                    self.sudoku_grid[i][j].set(str(m.evaluate(x[i][j])))

        else:
            print("No solution found")  # Printing a message if no solution is found

# Creating the main Tkinter window
root = tk.Tk()
app = SudokuSolverApp(root)  # Creating an instance of the SudokuSolverApp class
root.mainloop()  # Starting the Tkinter event loop

