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
# allocate variable names (see topology files in common dir for format)
switches = {} # switches
switches_temp = defaultdict(dict)
switches_cost = defaultdict(dict)
# all hosts, including low-capacity hosts but not transcoders
hosts = {}

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
final_trees = []
highest_link_usage = {}
algorithm = 'SIMPLE_SPT'
final_trees = defaultdict(dict)
final_trees_temp = []
highest_bw_usage = {}
MCAST_ADDR = "239.192.0.1"
DSCP_VALUE = 63 
sw_coor = {}
ho_coor ={}
tree_no3 = 1

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
    stack = [(start, [start], 0)]
    if start==goal:
    	yield [start]
    while stack:
        (vertex, path, cost) = stack.pop()
        print start
        print goal
        print path_len
        print path
        print cost
        for next in graph[vertex] - set(path):
            if next == goal and cost + switches[vertex][next]["cost"] == path_len:
                yield path + [next]
            elif cost + switches[vertex][next]["cost"] < path_len:
                stack.append((next, path + [next], cost + switches[vertex][next]["cost"]))
# Dijkstra's algorithm from switch src
def shortest_paths (src):
	dist = {}
	prev = {}

	tovisit = switches.keys()

	for node in tovisit:
		dist[node] = float('inf')
		prev[node] = None
	if src.find("h")!=-1:
		dist[src] = 0
	elif src.find("s")!=-1:
		dist[src] = 0

	while len(tovisit) > 0:
		# extract node u closest to the set of visited nodes
		tovisit.sort(key = lambda x: dist[x])
		u = tovisit.pop(0)
		# for each neighbor v of u still unvisited, update distances
		for v in switches[u]:
			if v in tovisit:
				if v.find("h")!=-1:
					tmp = dist[u] + switches[u][v]["cost"]
				elif v.find("s")!=-1:
					tmp = dist[u] + switches[u][v]["cost"]
				if tmp < dist[v]:
					dist[v] = tmp
					prev[v] = u
	return prev, dist


def shortest_paths_all(flow_rate):
	for s in switches:
		sp[s], distances[s] = shortest_paths(s)

def fill_sp1(sh, dhs):
	global switch_usage
	global sp1
	sp1.clear()
	switch_usage.clear()
	tree_match = {}
	temp_weight = {}
	temp_match = {}
	done = {}
	node_weights = {}
	path_listing = {}
	sorted_path_listing = {}
	src = sh
	for s in switches.keys():
		node_weights[s] = 0
		tree_match[s] = 0
		switch_usage[s] = []
	for dh in dhs:
		dst = dh
		leng = distances[src][dst]
		paths = list(dfs_paths(src, dst, leng))
		for i in range(len(paths)):
			for j in range(len(paths[i])):
				node_weights[paths[i][j]] += 1	
		path_listing[dh, leng] = paths
	for item in path_listing:
		print item, " ", path_listing[item]
		print

	sorted_path_listing = sorted(path_listing.items(), key = lambda x : len(x[1][0]))

	#for k in range(len(sorted_path_listing)):
		#print sorted_path_listing[k]
	
	for key in range(len(sorted_path_listing)):
		#print key
		temp = sorted_path_listing[key][1]
		temp_weight.clear()
		temp_match.clear()
		for i in range(len(temp)):
			temp_weight[i] = 0
			temp_match[i] = 0
		for i in range(len(temp)):
			for j in range(len(temp[i])):
				temp_weight[i] = temp_weight[i] + node_weights[temp[i][j]]
			for j in range(len(temp[i])):
				temp_match[i] = temp_match[i] + tree_match[temp[i][j]]

		sorted_temp_match = {}
		sorted_temp_weight = {}

		sorted_temp_match = sorted(temp_match.items(), key = lambda x: x[1])
		sorted_temp_weight = sorted(temp_weight.items(), key = lambda x: x[1])
		 

		temp_set = set()
		for k in range(len(sorted_temp_match)):
			temp_set.add(sorted_temp_match[k][1])

		if len(temp_set)==1:
			index = sorted_temp_weight[len(sorted_temp_weight)-1][0]
			sp1[sorted_path_listing[key][0][0]] = temp[index]
			for i in range(len(temp[index])):
				tree_match[temp[index][i]] = 1
				switch_usage[temp[index][i]].append(sorted_path_listing[key][0][0])
		else:
			index = sorted_temp_match[len(sorted_temp_match)-1][0]
			sp1[sorted_path_listing[key][0][0]] = temp[index]
			for i in range(len(temp[index])):
				tree_match[temp[index][i]] = 1
				switch_usage[temp[index][i]].append(sorted_path_listing[key][0][0])

	prev = {}
	for key in sp1.keys():
		path = sp1[key]
		for j in range(len(path)):
			if j-1 >= 0:	
				prev[path[j]] = path[j-1]
			else:
				prev[path[j]] = None

	sp[src] = prev 

def tree_ports_minedge (sh, dhs, flow_rate): # source host
	global dpids
	global dpids_cost
	edge_included = defaultdict(dict)
	switch_included = {}
	for sw in dpids:
		switch_included[sw] = False
	for src in switches:
		print src
		for dest in switches[src]:
			print dest
			edge_included[src][dest] = False
			edge_included[dest][src] = False

	fill_sp1(sh, dhs)
	done = set() # switches already part of the tree
	treeports = {}
	src = sh # source switch
	tree = copy.deepcopy(sp[sh])
	for dh in dhs: # high-capacity destination hosts
		if dh != sh:
			dst = dh # destination switch
			print dst
			if switch_included[dst] is False:
				dpids[dst]["cost"] = dpids[dst]["cost"]+dpids_cost[dst]["cost"]
				switch_included[dst] = True
			# walk back towards source until root (pre is None)
			# or another switch is found that is already part of the tree
			cur = dst # current switch
			pre = sp[src][cur] # parent of current switch
			while pre is not None and cur not in done and pre != sh:
				if switch_included[pre] is False:
					dpids[pre]["cost"] = dpids[pre]["cost"]+dpids_cost[pre]["cost"]
					switch_included[pre] = True

				if edge_included[cur][pre] is False:
					switches[pre][cur]["cost"] = switches[pre][cur]["cost"] + flow_rate*100
					switches[cur][pre]["cost"] = switches[cur][pre]["cost"] + flow_rate*100
					edge_included[pre][cur] = True
					edge_included[cur][pre] = True

				port = switches[pre][cur]["port"]
				if pre not in treeports:
					treeports[pre] = set()
				treeports[pre].add(port)
				# next iteration
				done.add(cur) # mark current switch as added to the tree
				cur = pre
				pre = sp[src][cur]

	return treeports, tree

def tree_ports_simple (sh, dhs, flow_rate): # source host
	edge_included = defaultdict(dict)
	switch_included = {}
	for sw in dpids:
		switch_included[sw] = False
	for src in switches:
		for dest in switches[src]:
			edge_included[src][dest] = False
			edge_included[dest][src] = False

	done = set() # switches already part of the tree
	treeports = {}
	src = hosts[sh]['switch'] # source switch
	tree = {}
	for dh in dhs:
		cur = dh
		pre = sp[sh][cur]
		while pre is not None and pre != sh:
			tree[cur] = pre
			cur = pre
			pre = sp[sh][cur]
		tree[cur] = pre
	#for child in sp[src]:
	#	tree[child] = sp[src][child]
	for dh in dhs: # high-capacity destination hosts
		if dh != sh:
			dst = hosts[dh]['switch'] # destination switch
			if switch_included[dst] is False:
				dpids[dst]["cost"] = dpids[dst]["cost"]+dpids_cost[dst]["cost"]
				switch_included[dst] = True
			# walk back towards source until root (pre is None)
			# or another switch is found that is already part of the tree
			cur = dst # current switch
			pre = sp[src][cur] # parent of current switch
			while pre is not None and cur not in done:
				if switch_included[pre] is False:
					dpids[pre]["cost"] = dpids[pre]["cost"]+dpids_cost[pre]["cost"]
					switch_included[pre] = True

				if edge_included[cur][pre] is False:
					switches[pre][cur]["cost"] = switches[pre][cur]["cost"] + flow_rate
					switches[cur][pre]["cost"] = switches[cur][pre]["cost"] + flow_rate
					edge_included[pre][cur] = True
					edge_included[cur][pre] = True

				port = switches[pre][cur]["port"]
				if pre not in treeports:
					treeports[pre] = set()
				treeports[pre].add(port)
				# next iteration
				done.add(cur) # mark current switch as added to the tree
				cur = pre
				pre = sp[src][cur]

			# add destination host
			if dst not in treeports:
				treeports[dst] = set()
			treeports[dst].add(hosts[dh]['port'])

	return treeports, tree

def fill_final_trees(tree_no, tree, sh, dhs, flow_rate, branch_state_nodes):
	global final_trees_temp
	global switches
	global dpids
	switches_toput = copy.deepcopy(switches)
	dpids_toput = copy.deepcopy(dpids)
	final_trees_temp += [{"tree_no":tree_no, "tree":tree, "sh":sh, "dhs":dhs, "flow_rate":flow_rate, "branch_state_nodes":branch_state_nodes, 
							"switches":switches_toput, "dpids":dpids_toput}]

def tree_ports_all(tree_no, sh, dhs, algorithm, flow_rate):
	global ports
	count = 0
	if(algorithm == "SIMPLE_SPT"):
		ports.clear()
		ports[sh], tree = tree_ports_simple(sh, dhs, flow_rate)
		print ports[sh]
		count , branch_state_nodes = install_simple_flows(tree)
		fill_final_trees(tree_no, tree, sh, dhs, flow_rate, branch_state_nodes)
	elif(algorithm == "MINEDGE_SPT"):
		ports.clear()
		ports[sh], tree = tree_ports_minedge(sh, dhs, flow_rate)
		print ports[sh]
		count, branch_state_nodes = install_simple_flows(tree)
		fill_final_trees(tree_no, tree, sh, dhs, flow_rate, branch_state_nodes)
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
		first = 1
		while cur is not None :
			if(len(ports[sh][cur])>1):
				if (first is not 1):
					port = switches[cur][pre]["port"]
					branch_node[dh] = cur, port
					break
				elif (first is 1):
					break
			elif(len(ports[sh][cur])==1):
				pre = cur
				cur = tree[cur]
			first = 0

	for dh in dhs:
		if branch_node[dh] is not None:
			branch_node_sw[branch_node[dh][0]] = 1

	for h in ports:
		for sw in ports[h]:
			degree[sw] = len(ports[h][sw]) + 1
			installed[sw] = 0

	for h in ports: # for each high-capacity source host
		for sw in ports[h]: # for each switch in the tree
			if (len(ports[h][sw])>1):
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
			if(len(ports[h][sw])==1):
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
	switches3 = final_trees[tree_no3]["switches"]
	dpids3 = final_trees[tree_no3]["dpids"]
	tree_no3 += 1
	print tree_no3
	algo_runner_obj.show_trees_from_final_trees(sh, dhs, switches3, hosts, dpids3, sw_coor, ho_coor, tree, branch_state_nodes)
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
	filejson = open("../topo/q_fattree_k_4_MINEDGE_SPT.json")
	#filejson = open("../topo/q_fattree_k_8_MINEDGE_SPT.json")
	#filejson = open("../topo/q_multicast_engg.json")
	#filejson = open("../topo/q_fattree_k_4_SIMPLE_SPT.json")
	topojson = json.load(filejson)
	entries = topojson['entries']
	entries = sorted(entries.items(), key = lambda x: int(x[0]))
	for k in range(len(entries)):
		print entries[k][0] , ":" , entries[k][1]
	src_file = entries[0][1]['src_file']
	load_json_topology("../topo/"+src_file)
	indexer = 0
	for k in range(len(entries)):
		print entries[k][0]
		entry = entries[k][1]
		#if int(entries[k][0]) == 6:
		#	break
		source = entry['src_host']
		destination = entry['dest_hosts']
		algorithm1 = entry['algorithm']
		algorithm = algorithm1
		flow_rate = entry['flow_rate']
		shortest_paths_all(flow_rate)
		#print "** Generating port sets for trees **"
		tree_no = int(entries[k][0])
		count = tree_ports_all(tree_no, source, destination, algorithm, flow_rate)
	for entry in final_trees:
		print entry
	evaluator_obj = evaluator(switches, hosts, dpids)
	evaluator_obj.save_final_trees(final_trees, final_trees_temp)
	evaluator_obj.evaluate(final_trees, "with_lb")
	show_final_trees()