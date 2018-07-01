from ofhelper import FlowEntry, GroupEntry
from collections import defaultdict
import matplotlib.pyplot as plt
import json
import operator
import copy
import random
# allocate variable names (see topology files in common dir for format)
max_level = 2
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
	switches.clear()
	hosts.clear()
	dpids.clear()
	gid.clear()
	graph.clear()

	filejson = open(filename)
	topojson = json.load(filejson)

	switches = topojson['switches']
	#switches_cost = topojson['switches']
	switches_cost = copy.deepcopy(switches)
	#print switches["s1"]["s2"]["cost"]

	hosts = topojson['hosts']
	dpids = topojson['dpids']
	dpids_cost = copy.deepcopy(dpids)

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
	adj_nodes = list(graph[dst])
	print adj_nodes
	for i in range(len(adj_nodes)):
		rand = random.randint(0, len(adj_nodes)-1)
		print "rand ",rand
		print dpids[adj_nodes[rand]]["level"]
		if dpids[adj_nodes[rand]]["level"] > dpids[dst]["level"]:
			return adj_nodes[rand]
		else:
			continue

	for i in range(len(adj_nodes)):
		if dpids[adj_nodes[i]]["level"] > dpids[dst]["level"]:
			return adj_nodes[i]

def BFS(dst, tree, graph, prev):
	global distances
	global sp
	src = None
	dist = float('inf')
	for node in tree:
		if distances[node][dst] < dist:
			src = node
			dist = distances[node][dst]
	print "Did BFS for ",dst, " and foune ",src," in the tree\n"
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
	for key in switches.keys():
		covered_set[key] = False
	covered_set[dst] = True
	for adj in switches[dst].keys():
		if adj in tree:
			print "found ",adj," in one level\n"
			prev[dst] = adj
			tree.add(dst)
			return tree, prev
		covered_set[adj] = True
	for adj in switches[dst].keys():
		for adj2 in switches[adj].keys():
			if covered_set[adj2] is False:
				if adj2 in tree:
					print "found ",adj2," in level two\n"
					prev[adj] = adj2
					prev[dst] = adj
					tree.add(adj)
					tree.add(dst)
					return tree,prev
				covered_set[adj2] = True
	if dpids[dst]["level"] < max_level:
		candidate = RandUpperNeigh(dst, graph)
		print "candidate is ",candidate
		tree1, prev1 = hook(src, candidate, dst_level)
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
	print "In the tree constructor"
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
	src = hosts[sh]['switch']
	print dhs
	for dh in dhs:
		covered_set.clear()
		print dh
		dst = hosts[dh]['switch']
		print dst
		if first is 1:
			print "Inside if"
			first = 0
			tree.add(dst) 
			prev, dist = shortest_paths(src)
			cur = dst
			pre = prev[cur]
			print dst
			while pre is not None:
				print "Inside while"
				print pre
				tree.add(pre)
				cur = pre
				pre = prev[cur]
		else:
			print "Inside else"
			print tree
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
	sp1[src] = tree_constructor(sh, dhs)
	for dh in dhs: # high-capacity destination hosts
		if dh != sh:
			dst = hosts[dh]['switch'] # destination switch
			if switch_included[dst] is False:
				dpids[dst]["capacity"] = dpids[dst]["capacity"]-2
				switch_included[dst] = True
			# walk back towards source until root (pre is None)
			# or another switch is found that is already part of the tree
			cur = dst # current switch
			pre = sp1[src][cur] # parent of current switch
			while pre is not None and cur not in done:
				if switch_included[pre] is False:
					dpids[pre]["capacity"] = dpids[pre]["capacity"]-2
					switch_included[pre] = True

				if edge_included[cur][pre] is False:
					switches[pre][cur]["capacity"] = switches[pre][cur]["capacity"] - flow_rate
					switches[cur][pre]["capacity"] = switches[cur][pre]["capacity"] - flow_rate
					edge_included[pre][cur] = True
					edge_included[cur][pre] = True

				port = switches[pre][cur]["port"]
				if pre not in treeports:
					treeports[pre] = set()
				treeports[pre].add(port)
				# next iteration
				done.add(cur) # mark current switch as added to the tree
				cur = pre
				pre = sp1[src][cur]

			# add destination host
			if dst not in treeports:
				treeports[dst] = set()
			treeports[dst].add(hosts[dh]['port'])

	return treeports

def tree_ports_all(sh, dhs, flow_rate):
	global ports
	count = 0
	ports.clear()
	ports[sh] = tree_ports_simple(sh, dhs, flow_rate)
	print ports[sh]
	count = install_simple_flows()
	return count

def reverse_path_port (host, switch):
	root = host['switch'] # root switch of h's tree
	pre = sp[root][switch] # parent switch of current switch
	if pre is None: # current switch is root switch
		return host['port'] # local port towards host
	else:
		return switches[switch][pre]["port"] # local port towards parent switch

def install_simple_flows():
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
	increment_mcast_addr()
	return count

def dump_sp():
	for s in sp:
		print "sp[%s]:%s" % (s, sp[s])
	print #newline

def evaluate():
	global switches_cost
	global switches
	global dpids
	global dpids_cost
	print

	link_included = defaultdict(dict)
	for src in switches:
		for dest in switches[src]:
			link_included[src][dest] = False

	bw_used = 0.0
	flows_used = 0.0
	num_links = 0.0
	num_switches = 0.0
	avg_link_usage = 0.0
	avg_switch_usage = 0.0
	highest_link_usage = 0.0
	lowest_link_usage = float("inf")
	for src in switches:
		for dest in switches[src]:
			if link_included[dest][src] is True:
				continue
			else:
				link_included[src][dest] = True
			if switches_cost[src][dest]["capacity"]>switches[src][dest]["capacity"]:
				bw_used = bw_used+switches_cost[src][dest]["capacity"]-switches[src][dest]["capacity"]
				num_links = num_links+1

	for src in switches:
		for dest in switches[src]:
			usage = switches_cost[src][dest]["capacity"]-switches[src][dest]["capacity"]
			if usage > highest_link_usage:
				highest_link_usage = usage
			if usage < lowest_link_usage:
				lowest_link_usage = usage

	if num_links>0:
		avg_link_usage = bw_used/num_links
	else:
		avg_link_usage=0

	for sw in dpids:
		if dpids_cost[sw]["capacity"]>dpids[sw]["capacity"]:
			flows_used = flows_used+dpids_cost[sw]["capacity"]-dpids[sw]["capacity"]
			num_switches = num_switches+1
	if num_switches>0:
		avg_switch_usage = flows_used/num_switches
	else:
		avg_switch_usage=0

	return avg_link_usage, avg_switch_usage, lowest_link_usage, highest_link_usage, bw_used, flows_used
			
if __name__ == "__main__":
	fw = open("result_avalanche.json","w")
	count = 0
	X_list = []
	Avg_link_list = []
	Avg_switch_list = []
	Highest_link_usage = []
	Lowest_link_usage = []
	Total_traffic = []
	Total_flows = []
	#filejson = open("../topo/q_fattree_minedge.json")
	#filejson = open("../topo/q_fattree_minedge_random.json")
	filejson = open("../topo/q_fattree_minedge_one.json")
	topojson = json.load(filejson)
	entries = topojson['entries']
	entries = sorted(entries.items(), key = lambda x: int(x[0]))
	'''for k in range(len(entries)):
		print entries[k][0] , ":" , entries[k][1]'''
	src_file = entries[0][1]['src_file']
	print src_file
	load_json_topology("../topo/"+src_file)
	indexer = 0

	shortest_paths_all()

	'''source = "h1"
	destination = ["h2","h3","h5","h7","h8","h11"]
	flow_rate = 1
	count = tree_ports_all(source, destination, flow_rate)
	print source, destination, algorithm, "Number of entries are :", count'''

	for k in range(len(entries)):
		#if k == 5:
		#	break
		print entries[k][0]
		entry = entries[k][1]


		source = entry['src_host']
		destination = entry['dest_hosts']
		algorithm = entry['algorithm']
		flow_rate = entry['flow_rate']
		#print "** Generating port sets for trees **"
		count = tree_ports_all(source, destination, flow_rate)
		print source, destination, algorithm, "Number of entries are :", count
		avg_link_usage,avg_switch_usage, lowest_link_usage, highest_link_usage, bw_used, flows_used = evaluate()
		indexer += 1
		X_list += [indexer]
		Avg_link_list += [avg_link_usage]
		Avg_switch_list += [avg_switch_usage]
		Highest_link_usage += [highest_link_usage]
		Lowest_link_usage += [lowest_link_usage]
		Total_traffic += [bw_used]
		Total_flows += [flows_used]
		print "avg_link_usage:",avg_link_usage,"avg_switch_usage:",avg_switch_usage
		print

	fw.write('{\n\"X_list\":"%s",\n'%X_list)
	fw.write('\"Avg_link_list\":"%s",\n'%Avg_link_list)
	fw.write('\"Avg_switch_list\":"%s",\n'%Avg_switch_list)
	fw.write('\"Highest_link_usage\":"%s",\n'%Highest_link_usage)
	fw.write('\"Lowest_link_usage\":"%s",\n'%Lowest_link_usage)
	fw.write('\"Total_traffic\":"%s",\n'%Total_traffic)
	fw.write('\"Total_flows\":"%s"\n}'%Total_flows)
