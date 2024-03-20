import tkinter as tk
import z3
from itertools import chain

class SudokuSolverApp:
    def __init__(self, master):
        self.master = master
        master.title("Sudoku Solver")

        self.sudoku_grid = [[tk.StringVar(master, '0') for _ in range(9)] for _ in range(9)]

        self.create_widgets()

    def create_widgets(self):
        for i in range(9):
            for j in range(9):
                entry = tk.Entry(self.master, width=2, textvariable=self.sudoku_grid[i][j], justify="center", font=("Arial", 16))
                entry.grid(row=i, column=j)
                if (i // 3 + j // 3) % 2 == 0:
                    entry.configure(bg="#f0f0f0")  # Light gray background for alternate cells
                else:
                    entry.configure(bg="#ffffff")  # White background for alternate cells
        
        solve_button = tk.Button(self.master, text="Solve", command=self.solve_sudoku, bg="#4CAF50", fg="white")
        solve_button.grid(row=9, column=4, pady=20)

    def solve_sudoku(self):
        x = [[z3.Int(f'x_{i}_{j}') for i in range(9)] for j in range(9)]
        range_c = [z3.And(i >= 1, i <= 9) for i in chain.from_iterable(x)]

        instance = [[int(var.get()) for var in row] for row in self.sudoku_grid]
        instance_c = [z3.If(instance[i][j] == 0, True, instance[i][j] == x[i][j])
                      for i in range(9) for j in range(9)]

        row_c = [z3.Distinct(i) for i in x]
        column_c = [z3.Distinct(list(chain.from_iterable(x))[i::9]) for i in range(9)]
        square_c = [z3.Distinct([x[j + l][i + k] for l in range(3) for k in range(3)])
                    for j in range(0, 9, 3) for i in range(0, 9, 3)]

        sudoku_c = range_c + instance_c + row_c + column_c + square_c

        solver = z3.Solver()
        solver.add(sudoku_c)

        if solver.check() == z3.sat:
            m = solver.model()
            for i in range(9):
                for j in range(9):
                    self.sudoku_grid[i][j].set(str(m.evaluate(x[i][j])))

        else:
            print("No solution found")

root = tk.Tk()
app = SudokuSolverApp(root)
root.mainloop()
