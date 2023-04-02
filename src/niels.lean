-- #eval Lean.versionString
import system.io

def main : io unit := io.print_ln "Hello, world!"

#eval main

def add (a b : nat) : nat :=
  a + b

#eval add 1 2

#eval string.append "Hello" "World"

def factorial (n : nat) : nat :=
  if n = 0 then 1 else n * factorial (n - 1)

#eval factorial 69

def sumn: nat → nat
| 0 := 0
| (n + 1) := n + 1 + sumn n

#eval sumn 10

def sumrec(n : nat) : nat :=
match n with
| 0 := 0
| (n + 1) := n + 1 + sumrec n

#eval sumrec 10