#!/bin/bash

BFS_DEPTH=4
DFS_DEPTH=50
DFS_SIMULATIONS=10
MODELS=("FaultModel" "Dynamic" "Monitors" "Exile" "Shadows" "UndoLogs")

trap 'echo "Exiting."; exit 1' SIGINT

# Check if tla2tools.jar is in the classpath
if [ ! -f tla2tools.jar ]; then
    echo "tla2tools.jar not found! Please download it."
    exit 1
fi

# Create the logs directory
if [ ! -d logs ]; then
    mkdir logs
fi

# Breadth-first search
bfs() {
    local model="$1"
    echo -n "Model checking the $model model... "
    sleep 1
    cmd="java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -dfid $BFS_DEPTH -config config/$model.cfg spec/$model.tla > logs/$model-bfs.log"
    if eval "$cmd"; then
        echo "Success."
    else
        echo "Errors detected! See logs/$model-bfs.log for details."
    fi
}

# Depth-first search
dfs() {
    local model="$1"
    echo -n "Model checking the $model model... "
    sleep 1
    cmd="java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -simulate num=$DFS_SIMULATIONS -depth $DFS_DEPTH -config config/$model.cfg spec/$model.tla > logs/$model-dfs.log"
    if eval "$cmd"; then
        echo "Success."
    else
        echo "Errors detected! See logs/$model-dfs.log for details."
    fi
}

echo "Breadth-first search:"
for model in "${MODELS[@]}"; do
    bfs "$model"
done

echo "Depth-first search:"
for model in "${MODELS[@]}"; do
    dfs "$model"
done