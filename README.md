
# Model checking

TLC (the TLA+ model checker) performs a breadth-first exhaustive search 
by default. Unfortunately, the models in this repository are unbounded and 
grow quickly as the search depth increases. Many bugs require ~10 steps to 
manifest---a depth that is already infeasible to search exhaustively. However,
random simulation is sufficient for finding most bugs within a few
minutes.

To search exhaustively up to depth N, pass the option `-dfid N` to TLC.

To simulate executions up to depth N, pass the option `-simulate -depth N`.
The depth defaults to 100.