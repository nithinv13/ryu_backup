from evaluator import evaluator
from ofhelper import FlowEntry, GroupEntry
from collections import defaultdict
from collections import Counter
from shapes_multi_engg import algo_runner
from Tkinter import *
from functools import partial
import ctypes
import numpy as np
#import matplotlib.pyplot as plt
import json
import operator
import copy
final_trees = defaultdict(dict)
final_trees_temp = []
highest_bw_usage = {}
# allocate variable names (see topology files in common dir for format)
switches = {} # switches
			  # switches
switches_temp = defaultdict(dict)
switches_cost = defaultdict(dict)
k = 0
# all hosts, including low-capacity hosts but not transcoders
hosts = {}
sw_coor = {}
ho_coor = {}

dpids = {} # datapath id for each switch
dpids_temp = {}
dpids_cost = {}
dpids_hosts = {}
dpids_hosts_cost = {}
dpids_hosts_temp = {}
# for each source host, store the list of output ports for each switch in tree
# used to build and track group entries
ports = {}
ports_lq = {}
# rooted at T
# shortest paths, from each switch
sp = {}
sp1 = {}
distances = {}
switch_usage = {}
# different groups may be installed on each switch (one for each source-specific
# tree traversing the switch): keep track of the next available group id
gid = {}
# the multicast address reserved to this group
graph = {}

algorithm = 'SIMPLE_SPT'
tree_no3 = 1
MCAST_ADDR = "239.192.0.1"
DSCP_VALUE = 63 

def load_json_topology (filename):

	global switches
	global hosts
	global dpids
	global gid
	global graph
	global switches_cost
	global dpids_cost
	global dpids_hosts
	global dpids_hosts_cost
	global switches_temp
	global dpids_temp
	global dpids_hosts_temp
	switches.clear()
	hosts.clear()
	dpids.clear()
	gid.clear()
	graph.clear()

	filejson = open(filename)
	topojson = json.load(filejson)

	switches = topojson['switches']
	switches_cost = copy.deepcopy(switches)
	switches_temp = copy.deepcopy(switches)
	hosts = topojson['hosts']
	dpids = topojson['dpids']
	dpids_hosts = topojson["dpids_hosts"]
	dpids_cost = copy.deepcopy(dpids)
	dpids_hosts_cost = copy.deepcopy(dpids_hosts)
	dpids_temp = copy.deepcopy(dpids)
	dpids_hosts_temp = copy.deepcopy(dpids_hosts)
	for i in range(len(switches)):
		graph[switches.keys()[i]] = set(switches[switches.keys()[i]].keys())

	for sw in switches:
		gid[sw] = 1

def get_next_gid (sw):
	g = gid[sw]
	gid[sw] += 1
	return g

def dfs_paths(start, goal, path_len):
	stack = [(start, [start], dpids_temp[start]["cost"])]
	if start == goal:
		yield [start]
	while stack:
	    (vertex, path, cost) = stack.pop()
	    for next1 in graph[vertex] - set(path):
	        if next1 == goal and cost+switches_temp[vertex][next1]["cost"]+dpids_temp[next1]["cost"] == path_len:
	            yield path + [next1]
            else:
                stack.append((next1, path + [next1], cost+switches_temp[vertex][next1]["cost"]+dpids_temp[next1]["cost"]))

def dfs_paths_less_than_path_len(start, goal, path_len):
	#print "inside dfs_paths_less than path length"
	if str(start).find("h")!= -1:
		stack = [(start, [start], dpids_hosts_temp[start]["cost"])]
	elif str(start).find("s")!=-1:
		stack = [(start, [start], dpids_temp[start]["cost"])]

	if start == goal:
		yield [start]

	while stack:
	    (vertex, path, cost) = stack.pop()
	    for next1 in graph[vertex] - set(path):

			if next1 == goal and str(next1).find("s")!=-1 and cost+switches_temp[vertex][next1]["cost"]+dpids_temp[next1]["cost"] <= path_len:
				yield path + [next1]
			if next1 == goal and str(next1).find("h")!=-1 and cost+switches_temp[vertex][next1]["cost"]+dpids_hosts_temp[next1]["cost"] <= path_len:
				yield path + [next1]
			else:
				if next1.find("s")!=-1:
					stack.append((next1, path + [next1], cost+switches_temp[vertex][next1]["cost"]+dpids_temp[next1]["cost"]))
				elif next1.find("h")!=-1:
					stack.append((next1, path + [next1], cost+switches_temp[vertex][next1]["cost"]+dpids_hosts_temp[next1]["cost"]))

			#print "Going out of dfs_paths less than path lenght"

# prev_tree:	 	set of n multicast trees stored in prev form
# senders: 		set of sender nodes for each multicast tree
# destinations:	set of destination nodes for each multicast tree

def is_overloaded(node, branch_nodes):
	if node.find('s')!=-1:
		if node not in branch_nodes:
			return False
		return len(branch_nodes[node]) > dpids[node]["capacity"]
	else: 
		return False

def is_full(node, branch_nodes, tree):
	if node.find("s")!=-1:
		if node not in branch_nodes:
			return False
		return tree not in branch_nodes[node] and len(branch_nodes[node]) == dpids[node]["capacity"]
	else:
		return True


def multicast_engg(prev_trees , senders, destinations): #switches
	branch_nodes = {}
	branch_nodes = find_branch_nodes(prev_trees, branch_nodes)
	print "branchnodes="
	for entry in branch_nodes:
		print str(entry)+" "
		for val in branch_nodes[entry]:
			print str(val)+" "+str(senders[id(val)])+" "+str(destinations[id(val)])
			print str(id(val))
		print

	prev_trees = multi_tree_routing_phase(prev_trees, senders, destinations, branch_nodes)

	for entry in prev_trees:
		print entry
		print
	
	branch_state_nodes = {}
	branch_state_nodes = state_node_assignment_phase(prev_trees, senders, destinations, branch_nodes, branch_state_nodes)
	print "branchnodes="
	for entry in branch_nodes:
		print str(entry)+" "
		for val in branch_nodes[entry]:
			print str(val)+" "+str(senders[id(val)])+" "+str(destinations[id(val)])
			print (str(id(val)))
		print
	

	print "branch_stat_nodes are:"
	for node in branch_state_nodes:
		print str(node)
		for tree in branch_state_nodes[node]:
			print str(tree)
		print
	branch_nodes = find_branch_nodes(prev_trees, branch_nodes)
	print "branch_nodes"
	for node in branch_nodes:
		print str(node)

	
	prev_trees, branch_state_nodes = local_search_phase(prev_trees, senders, destinations, branch_nodes, branch_state_nodes)
	print "branch_state_nodes after local search pahse are:"
	for node in branch_state_nodes:
		print str(node)
		for tree in branch_state_nodes[node]:
			print str(tree)
		print

	for entry in prev_trees:
		print entry

	return prev_trees, branch_state_nodes

def multi_tree_routing_phase(prev_trees, senders, destinations, branch_nodes):
	print "in multi_tree_routing_phase"
	u = None #overloaded node
	branch_nodes_temp = copy.deepcopy(branch_nodes)
	for node in branch_nodes_temp:
		if is_overloaded(node, branch_nodes):
			print node
			f, prev_trees = unload(node, prev_trees, senders, destinations, branch_nodes)
	return prev_trees

def find_downstream_branchstate_nodes(u, prev_trees, senders, destinations, branch_nodes):
	downstream_nodes = defaultdict(dict)
	for tree in branch_nodes[u]:
		if id(tree) not in downstream_nodes:
			downstream_nodes[id(tree)] = []
		for node in tree:
			if is_downstream(node, u, tree, branch_nodes, destinations):
				if str(node).find("s")!=-1 and (node in branch_nodes and tree in branch_nodes[node]):
					downstream_nodes[id(tree)] += [node]
				elif str(node).find("h")!=-1:
					downstream_nodes[id(tree)] += [node]

	return downstream_nodes

def is_down(a, b, tree):
	cur = a
	pre = tree[a]
	while pre is not None and pre!=cur:
		if pre == b:
			return True
		cur = pre
		pre = tree[cur]

def is_inbetween(u, v, w, tree):
	if is_down(v, w, tree) and is_down(w, u, tree):
		return True
	return False

def unload(u, prev_trees, senders, destinations, branch_nodes):
	breaking_condition = False
	print "in unload"
	downstream_nodes = find_downstream_branchstate_nodes(u, prev_trees, senders, destinations, branch_nodes)
	'''for entry in downstream_nodes:
		print str(entry)+" "+str(downstream_nodes[entry])
	for entry in branch_nodes[u]:
		print entry
		print id(entry)
		print'''
	print str(u)
	print str(downstream_nodes)
	for entry in downstream_nodes:
		if not is_overloaded(u, branch_nodes):
			break
		Ti = ctypes.cast(entry, ctypes.py_object).value
		for v in downstream_nodes[entry]:
			breaking_condition = False
			l = 0
			l = cost(u, v, Ti, l)
			print "cost "+str(u)+" "+str(v)+" "+str(l)
			for w in Ti:
				if w==v or w.find("h")!=-1 or is_inbetween(u, v, w, Ti):
					continue
				print str(w)
				if not is_full(w, branch_nodes, Ti) and not is_overloaded(w, branch_nodes):
					paths = list(dfs_paths_less_than_path_len(w, v, l))
					for path in paths:
						print str(path)
					for path in paths:
						if not is_intersecting(path, Ti, 0):
							print str(path)
							Ti = alievate(path, Ti, u, v)
							branch_nodes = find_branch_nodes(prev_trees, branch_nodes)
							breaking_condition = True
							break
					if breaking_condition is True:
						break
			if not is_overloaded(u, branch_nodes):
				break

	return True, prev_trees

def is_intersecting(path, prev, index):
	print "in is_intersecting"
	print path
	if index == len(path)-1:
		return False
	if len(path) <= 1:
		return False
	curr = path[index]
	if curr in prev and prev[curr] == path[index+1]:
		return True
	for node in prev:
		if prev[node] == curr and node == path[index+1]:
			return True
	return is_intersecting(path,prev, index+1)

def find_branch_nodes(prev_trees, branch_nodes):
	print "in branch nodes"
	branch_nodes.clear()
	index = 0
	for tree in prev_trees:
		c = Counter(tree.values()).most_common()
		#print index
		#print "c for tree: "+str(tree)
		#print c
		#print "c=", c
		for k,v in c:
			if k.find("s")!=-1:
				if tree[k]==k:
					v-=1
				if v >= 2:
					print str(k)
					if k not in branch_nodes:
						branch_nodes[k] = []
					branch_nodes[k]+=[tree]
	print "going out of branch nodes"
	return branch_nodes

def is_downstream(node, u, prev, branch_nodes, destinations):
	node = prev[node]
	while node != u:
		#print node
		if node in branch_nodes:
			if prev in branch_nodes[node] or node in destinations[id(prev)]:
				return False
		node = prev[node]
		if node == prev[node]:
			return False
	return True

def is_downstream_branch_state(node, u, prev, branch_state_nodes):
	node = prev[node]
	while node != u:
		#print node
		if node in branch_state_nodes:
			if prev in branch_state_nodes[node]:
				return False
		node = prev[node]
		if node == prev[node]:
			return False
	return True

def cost(u, v, prev, l):
	print "in cost"
	global switches
	if str(v).find("s")!=-1:
		l = dpids_cost[v]["cost"]
	elif str(v).find("h")!=-1:
		l = dpids_hosts_cost[v]["cost"]
	while v != u:
		p = prev[v]
		if p == v:
			break
		if p != None:
			if str(p).find("s")!=-1:
				l += switches[p][v]["cost"]+dpids_cost[p]["cost"]
			elif str(p).find("h")!=-1:
				l += switches[p][v]["cost"]+dpids_hosts_cost[p]["cost"]
		v = p
	return l

#def find_path(w, v, prev):


def alievate(path, prev, u, v):
	print "in alievate"
	print path
	print prev
	print u
	print v
	curr = prev[v]
	while curr!=u:
		print curr
		curr1 = prev[curr]
		prev.pop(curr)
		curr = curr1

	curr=path[0]
	for node in path[1:len(path)]:
		prev[node]=curr;
		curr=node
	print "after alievate"
	print prev
	return prev

def state_node_assignment_phase(prev_trees, senders, destinations, branch_nodes, branch_state_nodes):
	print "in state node assignment pahse"
	branch_state_nodes.clear()
	while is_branch_state_node_available(prev_trees,senders,destinations,branch_nodes,branch_state_nodes):
		branch_state_nodes = find_max_cost_reduction_branch_state_node_assignment(
			prev_trees, senders, destinations, branch_nodes, branch_state_nodes)
	return branch_state_nodes

def local_search_phase(prev_trees, senders, destinations, branch_nodes, branch_state_nodes):
	breaking_condition = False
	branch_state_nodes_temp = []
	print "in local search phase"
	for node in branch_state_nodes:
		print node
		if is_overloaded(node, branch_state_nodes):
			new_branch_state_tree = []
			for tree in branch_nodes[node]:
				cost1 = calculate_total_reduction_bandwidth_cost(tree, node, branch_state_nodes, destinations[id(tree)])
				new_branch_state_tree += [(cost1, tree)]
			new_branch_state_tree.sort(key=lambda x: x[0], reverse=True)
			for entry in new_branch_state_tree:
				print entry
			trees = [tup[1] for tup in new_branch_state_tree]
			if dpids[node]["capacity"] < len(trees):
				branch_state_nodes_temp[node] += [trees[0:dpids[node]["capacity"]]]
			else:
				branch_state_nodes_temp[node] += [trees[0:len(trees)-1]]
				#trees = trees[dpids[node]["capacity"]:]

	for entry in branch_state_nodes_temp:
		branch_state_nodes[entry] = copy.deepcopy(branch_state_nodes_temp[entry])

	print
	print "in second part of local search phase"
	print

	temp_branch_nodes = {}
	temp_branch_state_nodes = {}
	for node in branch_nodes:
		temp_branch_nodes[node] = []
		for tree in branch_nodes[node]:
			temp_branch_nodes[node] += [id(tree)]
	for node in branch_state_nodes:
		temp_branch_state_nodes[node] = []
		for tree in branch_state_nodes[node]:
			temp_branch_state_nodes[node] += [id(tree)]

	for node in branch_state_nodes:
		downstream_nodes = find_downstream_branchstate_nodes(node, prev_trees, senders, destinations, branch_nodes)
		temp_list = list(set(temp_branch_nodes[node])-set(temp_branch_state_nodes[node]))
		temp_list_tree = []
		for entry in temp_list:
			temp_list_tree += [ctypes.cast(entry, ctypes.py_object).value]
		for tree in temp_list_tree:
			u = node
			for v in downstream_nodes[id(tree)]:
				l = 0
				l = cost(u, v, tree, l)
				w = None
				breaking_condition = False
				for w in tree.keys():
					if w in branch_state_nodes and tree in branch_state_nodes[w]:
						paths = list(dfs_paths_less_than_path_len(w, v, l))
						for path in paths:
							if len(path) <= 1:
								continue
							if not is_intersecting(path, tree, 0):
								print "alievating for"
								print node
								print "paretn= "+str(u)
								print path
								tree = alievate(path, tree, u, v)
								breaking_condition = True
								break
					if breaking_condition is True:
						break

	return prev_trees, branch_state_nodes
	
def is_branch_state_node_available(prev_trees, senders, destinations, branch_nodes, branch_state_nodes):
	for node in branch_nodes:
		for tree in branch_nodes[node]: 
			if node not in branch_state_nodes and dpids[node]["capacity"]>0:
				return True
			if tree not in branch_state_nodes[node] and dpids[node]["capacity"]>len(branch_state_nodes[node]): 
				return True
			branch_state_nodes_id = []
			for tree1 in branch_state_nodes[node]:
				branch_state_nodes_id += [id(tree1)]
			if tree in branch_state_nodes[node] and id(tree) not in branch_state_nodes_id and dpids[node]["capacity"]>len(branch_state_nodes[node]):
				return True
	return False

def find_max_cost_reduction_branch_state_node_assignment(prev_trees, senders, destinations, branch_nodes, branch_state_nodes):
	print "in find_max_cost_reduction_branch_state_node_assignment"
	max_node=None
	max_tree=None
	max_cost=-sys.maxint + 1
	print max_cost
	for node in branch_nodes:
		for tree in branch_nodes[node]: 
			if node not in branch_state_nodes and dpids[node]["capacity"]>0:
				cost = calculate_total_reduction_bandwidth_cost(tree, node, branch_state_nodes, destinations[id(tree)])
				if cost > max_cost:
					max_cost, max_tree, max_node = cost, tree, node
			else:
				if tree not in branch_state_nodes[node] and dpids[node]["capacity"]>len(branch_state_nodes[node]): 
					cost = calculate_total_reduction_bandwidth_cost(tree, node, branch_state_nodes, destinations[id(tree)])
					if cost > max_cost:
						max_cost, max_tree, max_node = cost, tree, node

				branch_state_nodes_id = []
				for tree1 in branch_state_nodes[node]:
					branch_state_nodes_id += [id(tree1)]

				if tree in branch_state_nodes[node] and id(tree) not in branch_state_nodes_id and dpids[node]["capacity"]>len(branch_state_nodes[node]):
					cost = calculate_total_reduction_bandwidth_cost(tree, node, branch_state_nodes, destinations[id(tree)])
					if cost > max_cost:
						max_cost, max_tree, max_node = cost, tree, node
						
	print "max_node is "+str(max_node)
	print "max_cost is "+str(max_cost)
	print "max_tree is "+str(max_tree)
	if max_node not in branch_state_nodes:
		branch_state_nodes[max_node] = []
	branch_state_nodes[max_node] += [max_tree]
	return branch_state_nodes	

def calculate_total_reduction_bandwidth_cost(tree, node, branch_state_nodes, destination_nodes):
	downstream_branch_state_and_destination_nodes = find_downstream_branch_state_and_destination_nodes(
		tree, node, branch_state_nodes, destination_nodes)
	upstream_branch_state_node = find_upstream_branch_state_node(tree, node, branch_state_nodes)
	print downstream_branch_state_and_destination_nodes
	print upstream_branch_state_node
	cost1 = 0
	cost1 = cost(upstream_branch_state_node, node, tree, cost1)
	print cost1*(len(downstream_branch_state_and_destination_nodes)-1)
	return cost1*(len(downstream_branch_state_and_destination_nodes)-1)

def find_downstream_branch_state_and_destination_nodes(tree, cur_node, branch_state_nodes, destination_nodes):
	downstream_nodes=[]
	for node in branch_state_nodes:
		if tree in branch_state_nodes[node]:
			if is_downstream_branch_state(node, cur_node, tree, branch_state_nodes):
				downstream_nodes+=[node]
	for node in destination_nodes:
		#print id(tree)
		if is_downstream_branch_state(node, cur_node, tree, branch_state_nodes):
				downstream_nodes+=[node]
	return downstream_nodes

def find_upstream_branch_state_node(tree, cur_node, branch_state_nodes):
	print "in find_upsteam branch state node"
	#print "tree=",tree
	#print cur_node 
	cur_node = tree[cur_node]
	while tree[cur_node] != cur_node:
		#print cur_node
		if cur_node in branch_state_nodes and tree in branch_state_nodes[cur_node]:
			print "upstrem node is "+str(cur_node)
			return cur_node
		cur_node = tree[cur_node]
	return cur_node


# Shortest hop algorithm for shortest path
def shortest_hops_paths (src):
	dist = {}
	prev = {}
	q = Queue()
	tovisit = switches.keys();
	for node in tovisit:
		dist[node] = float('inf')
		prev[node] = None
	tovisit.pop(src);
	q.put(src);
	while not q.empty():
		u = q.get()
		neighbors = []
		for v in switches[u]:
			if v in tovisit:
				tmp = dist[u]  + switches_temp[u][v]["cost"] #dpids_temp[v]["cost"]
				heapq.heappush(neighbors, (v,tmp))
				dist[v]=tmp
				prev[v]=u
				tovisit.pop(v);
		while len(neighbors) > 0:
			q.put(neighbors[0][0])
			heapq.heappop(neighbors)[0]
	return prev, dist

# Dijkstra's algorithm from switch src
def shortest_paths (src):
	dist = {}
	prev = {}

	tovisit = switches.keys()

	for node in tovisit:
		dist[node] = float('inf')
		prev[node] = None

	if str(src).find("s")!=-1:
		dist[src] = dpids_temp[src]["cost"]
	elif str(src).find("h")!=-1:
		dist[src] = dpids_hosts_temp[src]["cost"]

	while len(tovisit) > 0:
		# extract node u closest to the set of visited nodes
		tovisit.sort(key = lambda x: dist[x])
		u = tovisit.pop(0)
		# for each neighbor v of u still unvisited, update distances
		for v in switches[u]:
			if v in tovisit:
				if str(v).find("s")!=-1:
					tmp = dist[u] + switches_temp[u][v]["cost"] + dpids_temp[v]["cost"]
				elif str(v).find("h")!=-1:
					tmp = dist[u] + switches_temp[u][v]["cost"] + dpids_hosts_temp[v]["cost"]
				if tmp < dist[v]:
					dist[v] = tmp
					prev[v] = u
	return prev, dist

def find_max_cap():
	global switches_temp
	global dpids_temp
	max_cap = 0
	for sw in dpids_temp:
		if dpids_temp[sw]["cost"] > max_cap:
			max_cap = dpids_temp[sw]["cost"]
	for src in switches:
		for dest in switches[src]:
			if switches[src][dest]["cost"] > max_cap:
				max_cap = switches[src][dest]["cost"]
	return max_cap

def shortest_paths_all():
	global switches
	global switches_temp
	global dpids
	global dpids_hosts
	global dpids_temp
	global dpids_hosts_temp
	switches_temp = copy.deepcopy(switches)
	dpids_temp = copy.deepcopy(dpids)
	dpids_hosts_temp = copy.deepcopy(dpids_hosts)

	for s in switches:
		sp[s], distances[s] = shortest_paths(s)

def reverse_path_port (host, switch):
	root = host['switch'] # root switch of h's tree
	pre = sp[root][switch] # parent switch of current switch
	if pre is None: # current switch is root switch
		return host['port'] # local port towards host
	else:
		return switches[switch][pre] # local port towards parent switch

'''def install_simple_flows():
	count = 0
	for h in ports: # for each high-capacity source host
		for sw in ports[h]: # for each switch in the tree
			# group entry
			newgid = get_next_gid(sw)
			g = GroupEntry(dpids[sw]["id"], newgid, "ALL")
			i = 0
			for p in ports[h][sw]: # for each switch port in the tree
				g.addBucket()
				g.addAction(i, "OUTPUT", port=p)
				i += 1
			g.install()
			count += 1
			# flow entry (also match on in_port for reverse path check)
			f = FlowEntry(dpids[sw]["id"])
			f.addMatch("in_port", reverse_path_port(hosts[h],sw))
			f.addMatch("dl_type", 0x800)
			f.addMatch("nw_src", hosts[h]['ip'])
			f.addMatch("nw_dst", MCAST_ADDR)
			f.addAction("GROUP", group_id=newgid)
			f.install()
			count += 1
	return count'''

def caller_for_multicast_engg(entries):
	global hosts
	global final_trees
	global final_trees_temp
	senders= {}
	destinations = {}
	prev_trees = []

	for k in entries:
		print k
		print type(k)
		entry = k[1]
		src_host = entry['src_host']
		dest_hosts = entry['dest_hosts']
		dest_switches = set()

		tree = copy.deepcopy(sp[src_host])

		new_tree = {}
		print new_tree
		print id(new_tree)

		for dest in dest_hosts:
			if dest not in new_tree:
				new_tree[dest] = tree[dest]
				dest = tree[dest]
				while dest != src_host:
					new_tree[dest] = tree[dest]
					dest = tree[dest]

		new_tree[src_host] = src_host
		senders[id(new_tree)]=src_host
		destinations[id(new_tree)] = dest_hosts
		prev_trees+=[new_tree]

	i = 0
	print "The shortest path trees"
	for entry in prev_trees:
		i += 1
		print i
		print entry
		print

	prev_trees, branch_state_nodes = multicast_engg(prev_trees , senders, destinations)
	print prev_trees
	print branch_state_nodes
	branch_state_nodes_transpose = {}
	for node in branch_state_nodes:
		for tree in branch_state_nodes[node]:
			if id(tree) in branch_state_nodes_transpose:
				branch_state_nodes_transpose[id(tree)]+=[node]
			else:
				branch_state_nodes_transpose[id(tree)] = []
				branch_state_nodes_transpose[id(tree)]+=[node]
		print tree in prev_trees, id(tree)  

	for k in entries:
		tree_no = int(k[0])
		src_host = k[1]["src_host"]
		dest_hosts = k[1]["dest_hosts"]
		flow_rate = k[1]["flow_rate"]
		tree = prev_trees[int(k[0])-1]
		if id(prev_trees[int(k[0])-1]) in branch_state_nodes_transpose:
			branch_state_nodes = branch_state_nodes_transpose[id(prev_trees[int(k[0])-1])] 
		else:
			branch_state_nodes = []
		final_trees_temp+=[{"tree_no":tree_no, "sh":src_host, "dhs":dest_hosts, "flow_rate":flow_rate, "tree":tree, "branch_state_nodes":branch_state_nodes }]
	print "final trees="
	for val in final_trees_temp:
		print val
	#return final_trees

def cal_bw_usage_for_single_tree(sh, dhs, tree, branch_state_nodes, flow_rate, src_switch, dest_switches, used):
	print "calculating bw for tree:" + str(id(tree))
	global hosts
	print dest_switches
	next_dest_switches = set()
	bw_used = 0
	for sw in dest_switches:

		cond = 0

		if sw == dest_switches[0]:
			next_dest_switches.clear()

		for switch in used:
			if str(sw).find(switch)!=-1:
				cond = 1
		if cond == 1:
			if sw == dest_switches[len(dest_switches)-1]:
				dest_switches = list(copy.deepcopy(next_dest_switches))
				break
			else:
				continue
		used += [sw]

		cur = sw
		pre = tree[sw]
		while pre not in branch_state_nodes and pre != src_switch and pre != None:
			#bw_used += flow_rate
			bw_used += switches[pre][cur]["cost"]
			cur = pre
			pre = tree[cur]
		if pre in branch_state_nodes:
			next_dest_switches.add(pre)
			#bw_used += flow_rate
			bw_used += switches[pre][cur]["cost"]
		elif pre == src_switch:
			#bw_used += flow_rate
			bw_used += switches[pre][cur]["cost"]
		elif pre == None:
			bw_used += 0

		if sw == dest_switches[len(dest_switches)-1]:
			dest_switches = list(copy.deepcopy(next_dest_switches))
			break

	if len(dest_switches)>0:
		bw_used = bw_used + cal_bw_usage_for_single_tree(sh, dhs, tree, branch_state_nodes, flow_rate, src_switch, dest_switches, used)

	return bw_used


def cal_bw_usage_from_final_trees():
	global final_trees
	bw_usages_all_trees = {}
	for entry in final_trees:
		used = []
		tree_no = final_trees[entry]["tree_no"]
		tree = final_trees[entry]["tree"]
		sh = final_trees[entry]["sh"]
		dhs = final_trees[entry]["dhs"]
		flow_rate = final_trees[entry]["flow_rate"]
		branch_state_nodes = final_trees[entry]["branch_state_nodes"]
		bw_usages_all_trees[tree_no] = cal_bw_usage_for_single_tree(sh, dhs, tree, branch_state_nodes, flow_rate, sh, dhs, used)
	return bw_usages_all_trees


def cal_flows_usage_from_final_trees():
	global final_trees
	flows_usage = {}
	for entry in final_trees:
		tree_no = final_trees[entry]["tree_no"]
		tree = final_trees[entry]["tree"]
		sh = final_trees[entry]["sh"]
		dhs = final_trees[entry]["dhs"]
		flow_rate = final_trees[entry]["flow_rate"]
		branch_state_nodes = final_trees[entry]["branch_state_nodes"]
		flows_usage[tree_no] = len(branch_state_nodes)
	return flows_usage

def cal_highest_link_usage():
	global final_trees
	global switches
	global highest_bw_usage
	highest_link_usage = defaultdict(dict)
	for src in switches:
		for dest in switches[src]:
			print src + "-" + dest
			highest_link_usage[src][dest] = 0
			highest_link_usage[dest][src] = 0
	print 
	for entry in final_trees:
		tree_no = final_trees[entry]["tree_no"]
		tree = final_trees[entry]["tree"]
		sh = final_trees[entry]["sh"]
		dhs = final_trees[entry]["dhs"]
		flow_rate = final_trees[entry]["flow_rate"]
		for src in tree:
			dest = tree[src]
			print src + "-" + dest
			if src != dest:
				highest_link_usage[src][dest] += flow_rate
				highest_link_usage[dest][src] += flow_rate
		result = 0
		for src in switches:
			for dest in switches[src]:
				if highest_link_usage[src][dest] > result:
					result = highest_link_usage[src][dest]
		highest_bw_usage[tree_no] = result
	
def evaluate():
	global highest_bw_usage
	global final_trees
	bw_usages_all_trees = cal_bw_usage_from_final_trees()
	flows_usage = cal_flows_usage_from_final_trees()
	for entry in bw_usages_all_trees:
		print str(entry) + ":" + str(bw_usages_all_trees[entry])
	for entry in flows_usage:
		print str(entry) + ":" + str(flows_usage[entry])
	cal_highest_link_usage()
	for tree_no in final_trees:
		final_trees[tree_no]["bw_usage"] = bw_usages_all_trees[tree_no]
		final_trees[tree_no]["flows_usage"] = flows_usage[tree_no]
		final_trees[tree_no]["highest_link_usage_till_now"] = highest_bw_usage[tree_no]
	X_list = []
	Highest_link_usage = []
	Total_traffic = []
	Total_flows = []
	total_traffic = 0
	total_flows = 0
	for entry in final_trees:
		X_list += [final_trees[entry]["tree_no"]]
		Highest_link_usage += [highest_bw_usage[final_trees[entry]["tree_no"]]]
		total_traffic += bw_usages_all_trees[final_trees[entry]["tree_no"]]
		Total_traffic += [total_traffic]
		total_flows += flows_usage[final_trees[entry]["tree_no"]]
		Total_flows += [total_flows]
	fw = open("/home/nithin/c/main_results/multicast_engg.json","w")
	fw.write('{\n\"X_list\":"%s",\n'%X_list)
	fw.write('\"Highest_link_usage\":"%s",\n'%Highest_link_usage)
	fw.write('\"Total_traffic\":"%s",\n'%Total_traffic)
	fw.write('\"Total_flows\":"%s"\n}'%Total_flows)

def caller_function(algo_runner_obj):
	global final_trees
	global tree_no3
	print tree_no3
	sh = final_trees[tree_no3]["sh"]
	dhs = final_trees[tree_no3]["dhs"]
	tree = final_trees[tree_no3]["tree"]
	branch_state_nodes = final_trees[tree_no3]["branch_state_nodes"]
	bw_usage = final_trees[tree_no3]["bw_usage"]
	flows_usage = final_trees[tree_no3]["flows_usage"]
	highest_till_now = final_trees[tree_no3]["highest_link_usage_till_now"]
	tree_no3 += 1
	print tree_no3
	algo_runner_obj.show_trees_from_final_trees(sh, dhs, switches, hosts, dpids, sw_coor, ho_coor, tree, branch_state_nodes)
	algo_runner_obj.print_specifics(sh, dhs, bw_usage, flows_usage, highest_till_now)

def show_final_trees():
	global final_trees
	print final_trees
	root = Tk()
	print type(hosts)
	algo_runner_obj = algo_runner(root, switches, hosts, dpids, sw_coor, ho_coor)
	button = Button(root, text = "Construce next tree", command = partial(caller_function, algo_runner_obj))
	button.pack()
	#print button
	root.mainloop()
			
if __name__ == "__main__":
	#filejson = open("../topo/netlab_and_jellyfish_files/q_netlab_lb_minedge.json")
	#filejson = open("../topo/q_fattree_minedge_multicast_engg_1.json")
	#filejson = open("../topo/q_fattree_minedge_single_src.json")
	#filejson = open("../topo/q_multicast_engg.json")
	filejson = open("../topo/q_fattree_k_4_MINEDGE_SPT.json")
	topojson = json.load(filejson)
	entries = topojson['entries']
	entries = sorted(entries.items(), key = lambda x: int(x[0]))

	
	src_file = entries[0][1]['src_file']
	#load_json_topology("../topo/netlab_and_jellyfish_files/"+src_file)
	load_json_topology("../topo/"+src_file)

	shortest_paths_all()
	caller_for_multicast_engg(entries)
	evaluator_obj = evaluator(switches, hosts, dpids)
	evaluator_obj.save_final_trees(final_trees, final_trees_temp)
	evaluator_obj.evaluate(final_trees, "multicast_engg")
	show_final_trees()