# eyelang
A basic programming language. The compiler is written in rust using LLVM as its backend.
Also contains a basic tree-walk interpreter that is being used for running programs right now until the LLVM backend is ready.

# Next steps
- [x] Correct typechecker
- [x] IR reducer
- [x] LLVM backend
- [ ] Pointers
- [ ] Arrays

# current tasks
- Definitions inside functions
- Flow analysis (return, assignment, etc.)
- Error position info during/after ir generation