# -*- coding: utf-8 -*-
"""
Created on Mon Nov  1 13:54:11 2021

@author: chote
"""

# Python3 implementation of the approach
import numpy as np

MAX = 100;

# Stores the vertices
store = [0]* MAX;

# Graph
graph = np.zeros((MAX, MAX));

# Degree of the vertices
d = [0] * MAX;

# Function to check if the given set of vertices
# in store array is a clique or not
def is_clique(b, matrix_inc, clique) :
    '''
    assert matrix_inc.shape[0] == matrix_inc.shape[1], "Wrong size of matrix"
    #all_vert = range(matrix_inc.shape[0]
    '''
	# Run a loop for all the set of edges
	# for the select vertex
    for i in range(1, b):
        for j in range(i + 1, b):

			# If any edge is missing
            if (matrix_inc[clique[i]][clique[j]] == 0) :
                return False;
	
    return True;

# Function to print the clique
def print_clique(n, clique) :

	for i in range(1, n) :
		print(clique[i], end = " ");
	print(",", end=" ");

# Function to find all the cliques of size s
def findCliques(matrix_inc, last_added, current_size, clique_size, accum, current_clique) :
    vertex_count = matrix_inc.shape[0]
	# Check if any vertices from i+1 can be inserted
    for j in range( last_added + 1, vertex_count -(clique_size - current_size) + 1) :

		# If the degree of the graph is sufficient
        if (d[j] >= clique_size - 1) :

			# Add the vertex to store
            current_clique[current_size] = j;

			# If the graph is not a clique of size k
			# then it cannot be a clique
			# by adding another vertex
            if (is_clique(current_size + 1, matrix_inc, current_clique)) :

				# If the length of the clique is
				# still less than the desired size
                if (current_size < clique_size) :

					# Recursion to add vertices
                    findCliques(matrix_inc, j, current_size + 1, clique_size, accum, current_clique)

				# Size is met
                else :
                    accum.append(current_clique[1:current_size+1])

# Driver code
if __name__ == "__main__" :

    edges = [ [ 1, 2 ],
			[ 2, 3 ],
			[ 3, 1 ],
			[ 4, 3 ],
			[ 4, 5 ],
			[ 5, 3 ] ];
    k = 3;
    size = len(edges);

    for i in range(len(edges)) :
        graph[edges[i][0]][edges[i][1]] = 1;
        graph[edges[i][1]][edges[i][0]] = 1;
        d[edges[i][0]] += 1;
        d[edges[i][1]] += 1;
        
    cliques = []
    vertexes = [graph.shape[0]
    findCliques(graph, 0, 1, k, cliques, store)
    print(cliques)
    