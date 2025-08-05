# Battleship Solitaire Solver 🚢

A Python AI program that solves **Battleship Solitaire puzzles** by formulating them as a **Constraint Satisfaction Problem (CSP)** and solving with **backtracking search**, **constraint propagation** (AC-3 / forward checking), and heuristics.  


---

## 📖 About the Project

**Battleship Solitaire** is a logic puzzle inspired by the game Battleship. Unlike the two-player version, a single-player puzzle provides:
- The number of ship parts in each row and column  
- The fleet composition (number of ships of each size)  
- Some squares already revealed as ship parts or water  

The goal is to deduce the exact locations of all ships while following placement rules.  

This solver leverages **CSP techniques** such as:
- **Backtracking Search**
- **Forward Checking / AC-3 Arc Consistency**
- **Heuristics** like Minimum Remaining Values (MRV), Degree Heuristic, and Least Constraining Value (LCV)

---

## 🧩 Puzzle Rules Implemented

- Four ship types:
  - Submarines (1×1)
  - Destroyers (1×2)
  - Cruisers (1×3)
  - Battleships (1×4)
- Ships are horizontal or vertical only (no diagonals)  
- Ships cannot touch each other, not even diagonally  
- Each row and column must match its ship-part count  
- Some cells may be prefilled with:
  - `S` = submarine  
  - `.` = water  
  - `< >` = ends of a horizontal ship  
  - `^ v` = ends of a vertical ship  
  - `M` = middle part of a ship  
  - `0` = unknown square  

---

## ⚙️ Features

- Encodes Battleship Solitaire as a **CSP**  
- Implements **AC-3** for arc consistency and pruning  
- Uses **backtracking with heuristics** for efficient search  
- Validates **row/column constraints** and **ship composition constraints**  
- Produces a complete board solution with no `0` placeholders  

---

## 🛠️ Tech Stack

- **Language**: Python 3  
- **Core Concepts**: CSP, Backtracking, AC-3, Heuristics  
- **Environment**: Linux
