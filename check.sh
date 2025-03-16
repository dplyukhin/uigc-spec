#!/bin/bash

# Breadth-first search
bfs() {
    local model="$1"
    echo -n "Model checking the $model model... "
    sleep 1
    cmd="java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -dfid 4 $model > $model-bfs.log"
    if eval "$cmd"; then
        echo "Success."
    else
        echo "Errors detected! See $model-bfs.log for details."
    fi
}

dfs() {
    local model="$1"
    echo -n "Model checking the $model model... "
    sleep 1
    cmd="java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -simulate num=10 -depth 50 $model > $model-dfs.log"
    if eval "$cmd"; then
        echo "Success."
    else
        echo "Errors detected! See $model-dfs.log for details."
    fi
}

echo "Breadth-first search:"
bfs "Dynamic"
bfs "Monitors"
bfs "Exile"
bfs "Shadows"
bfs "UndoLogs"

echo "Depth-first search:"
dfs "Dynamic"
dfs "Monitors"
dfs "Exile"
dfs "Shadows"
dfs "UndoLogs"