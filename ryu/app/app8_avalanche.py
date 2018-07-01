from evaluator import evaluator
from Tkinter import *
from ofhelper import FlowEntry, GroupEntry
from collections import defaultdict
import matplotlib.pyplot as plt
from functools import partial
from shapes_multi_engg import algo_runner
import json
import operator
import copy
import random
# allocate variable names (see topology files in common dir for format)
max_level = 3
covered_set = {}
prev = {}
switches = {} # switches
switches_temp = defaultdict(dict)
switches_cost = defaultdict(dict)
# all hosts, including low-capacity hosts but not transcoders
hosts = {}
tree = {"s1000"}

dpids = {} # datapath id for each switch
dpids_temp = {}
dpids_cost = {}
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
final_trees_temp = []
final_trees = defaultdict(dict)
sw_coor = {}
ho_coor = {}
highest_bw_usage = {}
tree_no3 = 1
MCAST_ADDR = "239.192.0.1"
DSCP_VALUE = 63 
all_dhs = []

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

def increment_mcast_addr():
	global MCAST_ADDR
	temp_addr = MCAST_ADDR.split(".")
	if int(temp_addr[3]) < 255:
		temp_addr[3] = str(int(temp_addr[3])+1)
	elif int(temp_addr[2]) < 255:
		temp_addr[2] = str(int(temp_addr[2])+1)
		temp_addr[3] = str(1)
	elif int(temp_addr[1]) < 255:
		temp_addr[1] = str(int(temp_addr[1])+1)
		temp_addr[2] = str(1)
		temp_addr[3] = str(1)
	elif int(temp_addr[0]) < 239:
		temp_addr[0] = str(int(temp_addr[0])+1)
		temp_addr[1] = str(1)
		temp_addr[2] = str(1)
		temp_addr[3] = str(1)
	MCAST_ADDR = temp_addr[0] + "." + temp_addr[1] + "." + temp_addr[2] + "." + temp_addr[3]

def get_next_gid (sw):
	g = gid[sw]
	gid[sw] += 1
	return g

# Dijkstra's algorithm from switch src
def shortest_paths (src):
	dist = {}
	prev = {}

	tovisit = switches.keys()

	for node in tovisit:
		dist[node] = float('inf')
		prev[node] = None

	dist[src] = 0

	while len(tovisit) > 0:
		# extract node u closest to the set of visited nodes
		tovisit.sort(key = lambda x: dist[x])
		u = tovisit.pop(0)
		# for each neighbor v of u still unvisited, update distances
		for v in switches[u]:
			if v in tovisit:
				tmp = dist[u] + 1
				if tmp < dist[v]:
					dist[v] = tmp
					prev[v] = u
	return prev, dist

def RandUpperNeigh(dst, graph):
	global dpids
	#print "in rand upper neigh"
	adj_nodes = list(graph[dst])
	#print adj_nodes
	while True:
	#for i in range(len(adj_nodes)):
		rand = random.randint(0, len(adj_nodes)-1)
		#print "rand ",rand
		#print dpids[adj_nodes[rand]]["level"]
		#print dpids[dst]["level"]
		if dpids[adj_nodes[rand]]["level"] > dpids[dst]["level"]:
			return adj_nodes[rand]
		else:
			continue

	'''for i in range(len(adj_nodes)):
		if dpids[adj_nodes[i]]["level"] > dpids[dst]["level"]:
			return adj_nodes[i]'''

def BFS(dst, tree, graph, prev):
	global distances
	global sp
	src = None
	dist = float('inf')
	for node in tree:
		if distances[node][dst] < dist:
			src = node
			dist = distances[node][dst]
	#print "Did BFS for ",dst, " and foune ",src," in the tree\n"
	tree.add(dst)
	cur = dst
	while pre in sp[src][cur] is not src:
		prev[cur] = pre
		tree.add(pre)
		cur = pre
	prev[cur] = src
	return tree, prev

def hook(src, dst, dst_level):
	global graph
	global max_level
	global covered_set
	global prev
	global tree
	global dpids
	for key in switches.keys():
		covered_set[key] = False
	covered_set[dst] = True
	for adj in switches[dst].keys():
		if adj in tree:
			#print "found ",adj," in one level\n"
			prev[dst] = adj
			tree.add(dst)
			return tree, prev
		covered_set[adj] = True
	for adj in switches[dst].keys():
		for adj2 in switches[adj].keys():
			if covered_set[adj2] is False:
				if adj2 in tree:
					#print "found ",adj2," in level two\n"
					prev[adj] = adj2
					prev[dst] = adj
					tree.add(adj)
					tree.add(dst)
					return tree,prev
				covered_set[adj2] = True
	if dst.find("s")!=-1 and dpids[dst]["level"] < max_level:
		candidate = RandUpperNeigh(dst, graph)
		#print "candidate is ",candidate
		tree1, prev1 = hook(src, candidate, dst_level+1)
		if tree1 is not None:
			prev[dst] = candidate
			tree.add(candidate)
			tree.add(dst)
	elif dst.find("h")!= -1 and dpids_hosts[dst]["level"] < max_level:
		candidate = RandUpperNeigh(dst, graph)
		#print "candidate is ",candidate
		tree1, prev1 = hook(src, candidate, dst_level+1)
		if tree1 is not None:
			prev[dst] = candidate
			tree.add(candidate)
			tree.add(dst)
	else:
		return None, prev

	if tree1 is None and dpids[dst]["level"] is 0:
		tree1, prev = BFS(dst, tree, graph, prev)
	return tree1, prev


def tree_constructor(sh, dhs):
	#print "In the tree constructor"
	global graph
	#print graph
	global tree
	global prev
	global covered_set
	prev.clear()
	tree1 = {"s1000"}
	tree = tree1
	#tree.clear()
	first = 1
	src = sh
	#print dhs

	for dh in dhs:
		covered_set.clear()
		#print dh
		dst = dh
		#print dst
		if first is 1:
			print "Inside if"
			first = 0
			tree.add(dst) 
			prev, dist = shortest_paths(src)
			prev_temp = {}
			cur = dst
			pre = prev[cur]
			while pre is not None:
				prev_temp[cur] = pre
				cur = pre
				pre = prev[cur]
			prev_temp[cur] = None
			prev.clear()
			prev = prev_temp
			cur = dst
			pre = prev[cur]
			#print dst
			while pre is not None:
				#print "Inside while"
				#print pre
				tree.add(pre)
				cur = pre
				pre = prev[cur]
		else:
			#print "Inside else"
			#print tree
			if dst in tree:
				continue
			for key in switches.keys():
				covered_set[key] = False
			covered_set[dst] = True
			zero = 0
			tree1, prev1 = hook(src, dst, zero)
			tree = tree1
			prev = prev1

	return prev


def shortest_paths_all():
	global switches
	global switches_temp
	global dpids
	global dpids_temp
	for s in switches:
		sp[s], distances[s] = shortest_paths(s)
	#print distances

def tree_ports_simple (sh, dhs, flow_rate): # source host
	sp1 = {}
	done = set() # switches already part of the tree
	treeports = {}
	src = sh # source switch
	sp1[sh] = tree_constructor(sh, dhs)
	tree3 = {}
	tree3 = copy.deepcopy(sp1[sh])
	for dh in dhs: # high-capacity destination hosts
		if dh != sh:
			dst = dh # destination switch
			# walk back towards source until root (pre is None)
			# or another switch is found that is already part of the tree
			cur = dst # current switch
			pre = sp1[src][cur] # parent of current switch
			while pre is not None and cur not in done and pre != sh:

				port = switches[pre][cur]["port"]
				if pre not in treeports:
					treeports[pre] = set()
				treeports[pre].add(port)
				# next iteration
				done.add(cur) # mark current switch as added to the tree
				cur = pre
				pre = sp1[src][cur]

	return treeports, tree3

def fill_final_trees(tree_no, tree, sh, dhs, flow_rate, branch_state_nodes):
	global final_trees_temp
	final_trees_temp += [{"tree_no":tree_no, "tree":tree, "sh":sh, "dhs":dhs, "flow_rate":flow_rate, "branch_state_nodes":branch_state_nodes}]

def cal_tree_cost(tree):
	return len(tree)-1

def gen_permutations(array, index):
	global all_dhs
	if index == len(array)-1:
		all_dhs += [copy.deepcopy(array)]
	for i in range(index, len(array)):
		temp = array[i]
		array[i] = array[index]
		array[index] = temp
		gen_permutations(array, index+1)
		temp = array[i]
		array[i] = array[index]
		array[index] = temp

def tree_ports_all(tree_no, sh, dhs, algorithm, flow_rate):
	global ports
	global all_dhs
	all_trees = []
	all_dhs = []
	#gen_permutations(dhs, 0)
	#print all_dhs
	all_dhs += [dhs]
	count = 0
	index = 1
	for dhs in all_dhs:
		ports.clear()
		ports[sh], tree = tree_ports_simple(sh, dhs, flow_rate)
		cost = cal_tree_cost(tree)
		all_trees += [(cost, copy.deepcopy(tree), copy.deepcopy(ports[sh]))]
	all_trees = sorted(all_trees, key= lambda x:x[0])
	tree = all_trees[0][1]
	ports[sh] = all_trees[0][2]
	#print ports[sh]
	#print tree
	count, branch_state_nodes = install_simple_flows(tree)
	fill_final_trees(tree_no, tree, sh, dhs, flow_rate, branch_state_nodes)


def reverse_path_port (host, switch, tree):
	#root = host['switch'] # root switch of h's tree
	#pre = sp[host][switch] # parent switch of current switch
	pre = tree[switch]
	if pre == host: # current switch is root switch
		return host['port'] # local port towards host
	else:
		return switches[switch][pre]["port"] # local port towards parent switch


def install_simple_flows(tree):
	count = 0
	branch_state_nodes = []
	for h in ports: # for each high-capacity source host
		for sw in ports[h]: # for each switch in the tree
			# group entry
			newgid = get_next_gid(sw)
			g = GroupEntry(dpids[sw]["id"], newgid, "ALL")
			i = 0
			#if len(ports[h][sw]) < 2 or dpids[sw]["capacity"] <= 0:
			#	continue
			branch_state_nodes += [sw]
			dpids[sw]["capacity"] -= 1
			for p in ports[h][sw]: # for each switch port in the tree
				g.addBucket()
				g.addAction(i, "OUTPUT", port=p)
				i += 1
			g.install()
			count += 1
			# flow entry (also match on in_port for reverse path check)
			f = FlowEntry(dpids[sw]["id"])
			f.addMatch("in_port", reverse_path_port(hosts[h],sw, tree))
			f.addMatch("dl_type", 0x800)
			f.addMatch("nw_src", hosts[h]['ip'])
			f.addMatch("nw_dst", MCAST_ADDR)
			f.addAction("GROUP", group_id=newgid)
			f.install()
			count += 1
	increment_mcast_addr()
	return count, branch_state_nodes

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
	#filejson = open("../topo/q_fattree_minedge_multicast_engg_1.json")
	#filejson = open("../topo/q_fattree_minedge_single_src.json")
	#filejson = open("../topo/q_multicast_engg.json")
	#filejson = open("../topo/q_fattree_k_4_MINEDGE_SPT.json")
	filejson = open("../topo/q_fattree_k_8_MINEDGE_SPT.json")
	#filejson = open("../topo/q_fattree_k_10_SIMPLE_SPT.json")
	topojson = json.load(filejson)
	entries = topojson['entries']
	entries = sorted(entries.items(), key = lambda x: int(x[0]))
	#for k in range(len(entries)):
	#	print entries[k][0] , ":" , entries[k][1]
	src_file = entries[0][1]['src_file']
	load_json_topology("../topo/"+src_file)
	indexer = 0
	shortest_paths_all()
	for k in range(len(entries)):
		#print entries[k][0]
		if int(entries[k][0]) == 501:
			break
		entry = entries[k][1]
		source = entry['src_host']
		destination = entry['dest_hosts']
		algorithm1 = entry['algorithm']
		algorithm = algorithm1
		flow_rate = entry['flow_rate']
		#print "** Generating port sets for trees **"
		tree_no = int(entries[k][0])
		count = tree_ports_all(tree_no, source, destination, algorithm, flow_rate)
	#for entry in final_trees:
	#	print entry
	evaluator_obj = evaluator(switches, hosts, dpids)
	evaluator_obj.save_final_trees(final_trees, final_trees_temp)
	evaluator_obj.evaluate(final_trees, "avalanche")
	show_final_trees()