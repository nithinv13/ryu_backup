from Tkinter import *
from evaluator import evaluator
from ofhelper import FlowEntry, GroupEntry
from collections import defaultdict
import matplotlib.pyplot as plt
from shapes_multi_engg import algo_runner
from functools import partial
import json
import operator
import copy
# allocate variable names (see topology files in common dir for format)
switches = {} # switches
switches_cost = defaultdict(dict)
final_trees = []
# all hosts, including low-capacity hosts but not transcoders
hosts = {}
dpids_hosts_temp = {}
dpids_temp = {}
switches_temp = {}
dpids = {} # datapath id for each switch
dpids_cost = defaultdict(dict)
dpids_hosts = {}
dpids_hosts_cost = defaultdict(dict)
# for each source host, store the list of output ports for each switch in tree
# used to build and track group entries
ports = {}
ports_lq = {}
# rooted at T
# shortest paths, from each switch
sp = defaultdict(dict)
sp1 = {}
distances = {}
switch_usage = {}
# different groups may be installed on each switch (one for each source-specific
# tree traversing the switch): keep track of the next available group id
gid = {}
# the multicast address reserved to this group
graph = {}
tree_no3 = 1
algorithm = 'SIMPLE_SPT'
final_trees = defaultdict(dict)
final_trees_temp = []
highest_bw_usage = {}
lowest_bw_usage = {}
sw_coor = {}
ho_coor = {}

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

def dfs_paths(start, goal, path_len):
    stack = [(start, [start])]
    if start==goal:
    	yield [start]
    while stack:
        (vertex, path) = stack.pop()
        for next in graph[vertex] - set(path):
            if next == goal and len(path) == path_len:
                yield path + [next]
            else:
                stack.append((next, path + [next]))

# Dijkstra's algorithm from switch src
def shortest_paths (src):
	dist = {}
	prev = {}

	tovisit = switches.keys()

	for node in tovisit:
		dist[node] = float('inf')
		prev[node] = None
	if src.find("h")!=-1:
		dist[src] = dpids_hosts_temp[src]["cost"]
	elif src.find("s")!=-1:
		dist[src] = dpids_temp[src]["cost"]

	while len(tovisit) > 0:
		# extract node u closest to the set of visited nodes
		tovisit.sort(key = lambda x: dist[x])
		u = tovisit.pop(0)
		# for each neighbor v of u still unvisited, update distances
		for v in switches[u]:
			if v in tovisit:
				if v.find("h")!=-1:
					tmp = dist[u] + 1
				elif v.find("s")!=-1:
					tmp = dist[u] + 1
				if tmp < dist[v]:
					dist[v] = tmp
					prev[v] = u
	return prev, dist

def shortest_paths_all(flow_rate):
	for s in switches:
		sp[s], distances[s] = shortest_paths(s)

def tree_ports_simple (sh, dhs, flow_rate, tree): # source host
	global switches
	done = set() # switches already part of the tree
	treeports = {}
	src = sh
	for dh in dhs: # high-capacity destination hosts
		if dh != sh:
			dst = dh # destination switch
			# walk back towards source until root (pre is None)
			# or another switch is found that is already part of the tree
			cur = dst # current switch
			pre = sp[src][cur] # parent of current switch
			while pre is not None and cur not in done and pre != sh:
				port = switches[pre][cur]["port"]
				if pre not in treeports:
					treeports[pre] = set()
				treeports[pre].add(port)
				# next iteration
				done.add(cur) # mark current switch as added to the tree
				cur = pre
				pre = sp[src][cur]


	return treeports

def fill_final_trees(tree_no, tree, sh, dhs, flow_rate, branch_state_nodes):
	global final_trees_temp
	final_trees_temp += [{"tree_no":tree_no, "tree":tree, "sh":sh, "dhs":dhs, "flow_rate":flow_rate, "branch_state_nodes":branch_state_nodes}]

def get_pod_for_edge_switch(k, n):
	print k
	pod = 1
	if (n-pow(k/2, 2)-pow(k, 2)/2)%(k/2) != 0:
		pod = (n-pow(k/2, 2)-pow(k, 2)/2)/(k/2) + 1
	else:
		pod = (n-pow(k/2, 2)-pow(k, 2)/2)/(k/2)
	return pod

def fill_aggr_switches(k, edge_switches_in_tree):
	global switches
	cost = 0
	aggr_swiches_cost = {}
	aggr_swiches_in_tree = {}
	for i in range(1, k/2 + 1):
		cost = 0
		for pod in edge_switches_in_tree:
			aggr_sw_num = pow(k/2, 2) + (pod-1)*(k/2) + i
			aggr_sw = "s"+str(aggr_sw_num)
			for edge_sw in edge_switches_in_tree[pod]:
				cost += switches[aggr_sw][edge_sw]["cost"]
		aggr_swiches_cost[i] = cost

	print edge_switches_in_tree
	print aggr_swiches_cost
	aggr_swiches_cost = sorted(aggr_swiches_cost.items(), key = lambda x:x[1])
	print aggr_swiches_cost
	req_aggr_sw_num = aggr_swiches_cost[0][0]
	for pod in edge_switches_in_tree:
		aggr_sw_num = pow(k/2, 2) + (pod-1)*(k/2) + req_aggr_sw_num
		aggr_sw = "s"+str(aggr_sw_num)
		for sw in switches.keys():
			if sw == aggr_sw:
				aggr_sw = sw
		aggr_swiches_in_tree[pod] = aggr_sw

	return aggr_swiches_in_tree, req_aggr_sw_num

def fill_core_switch(k, req_aggr_sw_num, aggr_swiches_in_tree):
	core_switches_cost = {}
	for i in range((req_aggr_sw_num-1)*k/2 + 1, (req_aggr_sw_num-1)*k/2 + k/2 +1):
		core_sw = "s"+str(i)
		cost = 0
		for pod in aggr_swiches_in_tree:
			aggr_sw = aggr_swiches_in_tree[pod]
			cost += switches[core_sw][aggr_sw]["cost"]
		core_switches_cost[i] = cost

	core_switches_cost = sorted(core_switches_cost.items(), key = lambda x: x[1])
	core_sw_num = core_switches_cost[0][0]
	core_sw = "s"+str(core_sw_num)
	#core_sw = unicode(core_sw, "utf-8")
	for sw in switches.keys():
		if sw == core_sw:
			core_sw = sw
	return core_sw

def fill_aggr_and_core_switches(k, edge_switches_in_tree):
	min_cost = sys.maxint
	for aggr_sw_num_rel in range(1, k/2+1):
		for core_sw_num_rel in range(1, k/2+1):
			core_sw_num = (aggr_sw_num_rel-1)*k/2 + core_sw_num_rel
			core_sw = "s"+str(core_sw_num) 
			cost = 0
			for pod in edge_switches_in_tree:
				aggr_sw_num = pow(k/2, 2) + (pod-1)*k/2 +aggr_sw_num_rel
				aggr_sw = "s"+str(aggr_sw_num)
				cost += switches[core_sw][aggr_sw]["cost"]
				for edge_sw in edge_switches_in_tree[pod]:
					cost += switches[edge_sw][aggr_sw]["cost"]
			if cost < min_cost:
				min_cost = cost
				req_aggr_sw_rel = aggr_sw_num_rel
				req_core_sw_rel = core_sw_num_rel

	aggr_swiches_in_tree = {}
	for pod in edge_switches_in_tree:
		aggr_sw_num = pow(k/2, 2) + (pod-1)*k/2 + req_aggr_sw_rel
		aggr_swiches_in_tree[pod] = "s" + str(aggr_sw_num)

	core_sw_num = (req_aggr_sw_rel-1)*k/2 + req_core_sw_rel
	core_sw = "s" + str(core_sw_num)

	return aggr_swiches_in_tree, core_sw

def make_tree(k, sh, dhs, flow_rate):
	print k
	global switches
	global hosts
	edge_switches_cost = {}
	edge_switches_in_tree = {}
	tree = {}
	tree[sh] = sh
	sw = copy.deepcopy(hosts[sh]["switch"])
	tree[hosts[sh]["switch"]] = sh
	pod = get_pod_for_edge_switch(k, int(sw.replace("s", "")))
	if pod not in edge_switches_in_tree:
		edge_switches_in_tree[pod] = []
	if str(hosts[sh]["switch"]) not in edge_switches_in_tree[pod]:
		edge_switches_in_tree[pod] += [hosts[sh]["switch"]] 

	for dh in dhs:
		sw = copy.deepcopy(hosts[dh]["switch"])
		tree[dh] = hosts[dh]["switch"]
		pod = get_pod_for_edge_switch(k, int(sw.replace("s", "")))
		if pod not in edge_switches_in_tree:
			edge_switches_in_tree[pod] = []
		if hosts[dh]["switch"] not in edge_switches_in_tree[pod]:
			edge_switches_in_tree[pod] += [hosts[dh]["switch"]]

	#aggr_swiches_in_tree, req_aggr_sw_num = fill_aggr_switches(k, edge_switches_in_tree)
	#core_switch = fill_core_switch(k, req_aggr_sw_num, aggr_swiches_in_tree)

	aggr_swiches_in_tree, core_switch = fill_aggr_and_core_switches(k, edge_switches_in_tree)

	src_pod = 1
	hosts_in_a_pod = pow(k/2, 2)
	if int(sh.replace("h", ""))%hosts_in_a_pod == 0:
		src_pod = int(sh.replace("h", ""))/hosts_in_a_pod
	else:
		src_pod = int(sh.replace("h", ""))/hosts_in_a_pod+1

	for pod in edge_switches_in_tree:
		for edge_sw in edge_switches_in_tree[pod]:
			if edge_sw != hosts[sh]["switch"]:
				tree[edge_sw] = aggr_swiches_in_tree[pod]

	tree[aggr_swiches_in_tree[src_pod]] = hosts[sh]["switch"]
	tree[core_switch] = aggr_swiches_in_tree[src_pod]
	for pod in aggr_swiches_in_tree:
		if pod != src_pod:
			tree[aggr_swiches_in_tree[pod]] = core_switch

	return tree

def change_switch_weights(tree, flow_rate):
	global switches
	for src in tree:
		dest = tree[src]
		if src != dest:
			switches[src][dest]["cost"] += flow_rate
			switches[dest][src]["cost"] += flow_rate

def tree_ports_all(k, tree_no, sh, dhs, algorithm, flow_rate):
	print "in tree_ports_all"
	print k
	global ports
	count = 0
	#if(algorithm == "SIMPLE_SPT"):
	print "in the algo"
	#print switches
	ports.clear()
	tree = make_tree(k, sh, dhs, flow_rate)
	print tree
	sp[sh] = copy.deepcopy(tree)
	ports[sh] = tree_ports_simple(sh, dhs, flow_rate, tree)
	change_switch_weights(tree, flow_rate)
	print "ports are"
	print ports[sh]
	#count, branch_state_nodes = install_simple_flows(tree)
	count, branch_state_nodes = install_branch_aware_flows(sh, dhs, tree)
	fill_final_trees(tree_no, tree, sh, dhs, flow_rate, branch_state_nodes)
	'''elif(algorithm == "MINEDGE_SPT"):
		ports.clear()
		ports[sh], tree = tree_ports_minedge(sh, dhs, flow_rate)
		print "tree_no" + str(tree_no)
		print "ports are"
		print ports[sh]
		count, branch_state_nodes = install_simple_flows()
		fill_final_trees(tree_no, tree, sh, dhs, flow_rate, branch_state_nodes)'''
	return count

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
			#if len(ports[h][sw]) < 2 or dpids[sw]["capacity"] <= 0:
			#	continue
			newgid = get_next_gid(sw)
			g = GroupEntry(dpids[sw]["id"], newgid, "ALL")
			i = 0
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

def install_branch_aware_flows(sh, dhs, tree):
	global switch_usage
	count = 0
	branch_node = {}
	degree = {}
	installed = {}
	branch_node_sw = {}
	branch_state_nodes = []

	src = hosts[sh]['switch']

	for dh in dhs:
		branch_node[dh] = None

	for sw in switches.keys():
		branch_node_sw[sw] = 0

	for dh in dhs:
		dst = hosts[dh]['switch']
		cur = dst
		pre = dh
		first = 0
		while cur != sh :
			if(len(ports[sh][cur])>1):
				if (first != 1):
					port = switches[cur][pre]["port"]
					branch_node[dh] = cur, port
					break
			elif(len(ports[sh][cur])==1):
				pre = cur
				cur = tree[cur]

	for dh in dhs:
		if branch_node[dh] is not None:
			branch_node_sw[branch_node[dh][0]] = 1
			cur = branch_node[dh][0]
			pre = tree[cur]
			while pre != sh:
				branch_node_sw[cur] = 1
				cur = pre
				pre = tree[cur]
			if pre == sh:
				branch_node_sw[hosts[sh]["switch"]] = 1

	for h in ports:
		for sw in ports[h]:
			degree[sw] = len(ports[h][sw]) + 1
			installed[sw] = 0

	for h in ports: # for each high-capacity source host
		for sw in ports[h]: # for each switch in the tree
			if (branch_node_sw[sw] == 1):
				branch_state_nodes += [sw]
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
				dpids[sw]["capacity"] = dpids[sw]["capacity"]-1
				# flow entry (also match on in_port for reverse path check)
				f = FlowEntry(dpids[sw]["id"])
				f.addMatch("in_port", reverse_path_port(hosts[h],sw, tree))
				f.addMatch("dl_type", 0x800)
				f.addMatch("nw_src", hosts[h]['ip'])
				f.addMatch("nw_dst", MCAST_ADDR)
				f.addAction("GROUP", group_id=newgid)
				f.install()
				count += 1

	for h in ports:
		for dh in dhs:
			if branch_node[dh] is not None:
				sw, p = branch_node[dh]
				if sw is not None:
					f = FlowEntry(dpids[sw]["id"])
					f.addMatch("in_port", reverse_path_port(hosts[h],sw, tree))
					f.addMatch("dl_type", 0x800)
					f.addMatch("nw_dst", MCAST_ADDR)
					f.addAction("SET_FIELD", field="ipv4_dst", value=hosts[dh]['ip'])
					f.addAction("OUTPUT", port = p)
					f.install()
					count += 1

	for h in ports:
		i = 0
		for sw in ports[h]:
			if(len(ports[h][sw])==1 and branch_node_sw[sw]!=1):
				f = FlowEntry(dpids[sw]["id"])
				f.addMatch("in_port", reverse_path_port(hosts[h],sw, tree))
				f.addMatch("dl_type", 0x800)
				f.addMatch("nw_src", hosts[h]['ip'])
				#f.addMatch("nw_dst", hosts[switch_usage[sw][0]]['ip'])
				for p in ports[h][sw]:
					f.addAction("OUTPUT", port = p)
				f.install()
				i += 1
	increment_mcast_addr()
	return count, branch_state_nodes

def save_final_trees():
	global final_trees_temp
	global final_trees
	for val in final_trees_temp:
			final_trees[val["tree_no"]]["tree_no"] = val["tree_no"]
			final_trees[val["tree_no"]]["tree"] = val["tree"]
			final_trees[val["tree_no"]]["branch_state_nodes"] = val["branch_state_nodes"]
			final_trees[val["tree_no"]]["sh"] = val["sh"]
			final_trees[val["tree_no"]]["dhs"] = val["dhs"]
			final_trees[val["tree_no"]]["flow_rate"] = val["flow_rate"]

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
	#filejson = open("../topo/q_fattree_minedge.json")
	#filejson = open("../topo/q_fattree_minedge_random.json")
	#filejson = open("../topo/q_fattree_minedge_multicast_engg_1.json")
	#filejson = open("../topo/q_fattree_minedge_single_src.json")
	#filejson = open("../topo/q_fattree_minedge_single_src_SIMPLE_SPT.json")
	#filejson = open("../topo/q_multicast_engg.json")
	#filejson = open("../topo/q_fattree_k_4_SIMPLE_SPT.json")
	filejson = open("../topo/q_fattree_k_8_SIMPLE_SPT.json")
	#filejson = open("../topo/q_fattree_k_10_SIMPLE_SPT.json")
	topology_k = 8
	topojson = json.load(filejson)
	entries = topojson['entries']
	entries = sorted(entries.items(), key = lambda x: int(x[0]))
	'''for k in range(len(entries)):
		print entries[k][0] , ":" , entries[k][1]'''
	src_file = entries[0][1]['src_file']
	load_json_topology("../topo/"+src_file)
	indexer = 0
	shortest_paths_all(1)
	for k in range(len(entries)):
		print entries[k][0]
		if int(entries[k][0]) == 501:
			break
		entry = entries[k][1]
		source = entry['src_host']
		destination = entry['dest_hosts']
		algorithm1 = entry['algorithm']
		algorithm = algorithm1
		flow_rate = entry['flow_rate']
		#shortest_paths_all(flow_rate)
		#print "** Generating port sets for trees **"
		tree_no = int(entries[k][0])
		count = tree_ports_all(topology_k, tree_no, source, destination, algorithm, flow_rate)
	for entry in final_trees:
		print entry
	
	evaluator_obj = evaluator(switches, hosts, dpids)
	evaluator_obj.save_final_trees(final_trees, final_trees_temp)
	evaluator_obj.evaluate(final_trees, "FTLB")
	#save_final_trees()
	show_final_trees()