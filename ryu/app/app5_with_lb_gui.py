from ofhelper import FlowEntry, GroupEntry
from collections import defaultdict
from shapes import algo_runner
from Tkinter import *
from functools import partial
#import matplotlib.pyplot as plt
import json
import operator
import copy
# allocate variable names (see topology files in common dir for format)
switches = {} # switches
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

def dfs_paths(start, goal, path_len):
    stack = [(start, [start], dpids_temp[start]["cost"])]
    if start == goal:
    	yield [start]
    while stack:
        (vertex, path, cost) = stack.pop()
        for next in graph[vertex] - set(path):
            if next == goal and cost+switches_temp[vertex][next]["cost"]+dpids_temp[next]["cost"] == path_len:
                yield path + [next]
            else:
                stack.append((next, path + [next], cost+switches_temp[vertex][next]["cost"]+dpids_temp[next]["cost"]))

# Dijkstra's algorithm from switch src
def shortest_paths (src):
	dist = {}
	prev = {}

	tovisit = switches.keys()

	for node in tovisit:
		dist[node] = float('inf')
		prev[node] = None
	dist[src] = dpids_temp[src]["cost"]

	while len(tovisit) > 0:
		# extract node u closest to the set of visited nodes
		tovisit.sort(key = lambda x: dist[x])
		u = tovisit.pop(0)
		# for each neighbor v of u still unvisited, update distances
		for v in switches[u]:
			if v in tovisit:
				tmp = dist[u] + switches_temp[u][v]["cost"] + dpids_temp[v]["cost"]
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


def update_switches_temp(flow_rate):
	max_cap = find_max_cap()
	for src in switches_temp:
		for dest in switches_temp[src]:
			if switches[src][dest]["capacity"] < flow_rate:
				switches_temp[src][dest]["cost"] = max_cap
				switches_temp[dest][src]["cost"] = max_cap
	for sw in dpids_temp:
		if dpids[sw]["capacity"] <= 0:
			dpids_temp[sw]["cost"] = max_cap

def shortest_paths_all(flow_rate):
	global switches
	global switches_temp
	global dpids
	global dpids_temp
	switches_temp = copy.deepcopy(switches)
	dpids_temp = copy.deepcopy(dpids)
	update_switches_temp(flow_rate)
	for s in switches:
		sp[s], distances[s] = shortest_paths(s)
	print distances

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
	src = hosts[sh]['switch']
	for s in switches.keys():
		node_weights[s] = 0
		tree_match[s] = 0
		switch_usage[s] = []
	for dh in dhs:
		dst = hosts[dh]['switch']
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
	src = hosts[sh]['switch'] # source switch
	
	for dh in dhs: # high-capacity destination hosts
		if dh != sh:
			dst = hosts[dh]['switch'] # destination switch
			print dst
			if switch_included[dst] is False:
				dpids[dst]["cost"] = dpids[dst]["cost"]+dpids_cost[dst]["cost"]*2
				if algorithm != "BRANCH_AWARE":
					dpids[dst]["capacity"] = dpids[dst]["capacity"]-2
				switch_included[dst] = True
			# walk back towards source until root (pre is None)
			# or another switch is found that is already part of the tree
			cur = dst # current switch
			pre = sp[src][cur] # parent of current switch
			while pre is not None and cur not in done:
				if switch_included[pre] is False:
					dpids[pre]["cost"] = dpids[pre]["cost"]+dpids_cost[pre]["cost"]
					if algorithm != "BRANCH_AWARE":
						dpids[pre]["capacity"] = dpids[pre]["capacity"]-2
					switch_included[pre] = True

				if edge_included[cur][pre] is False:
					switches[pre][cur]["cost"] = switches[pre][cur]["cost"] + switches_cost[pre][cur]["cost"]*flow_rate
					switches[cur][pre]["cost"] = switches[cur][pre]["cost"] + switches_cost[cur][pre]["cost"]*flow_rate
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
				pre = sp[src][cur]
				

			# add destination host
			if dst not in treeports:
				treeports[dst] = set()
			treeports[dst].add(hosts[dh]['port'])

	return treeports

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
	for dh in dhs: # high-capacity destination hosts
		if dh != sh:
			dst = hosts[dh]['switch'] # destination switch
			if switch_included[dst] is False:
				dpids[dst]["cost"] = dpids[dst]["cost"]+dpids_cost[dst]["cost"]
				if algorithm != "BRANCH_AWARE":
					dpids[dst]["capacity"] = dpids[dst]["capacity"]-2
				switch_included[dst] = True
			# walk back towards source until root (pre is None)
			# or another switch is found that is already part of the tree
			cur = dst # current switch
			pre = sp[src][cur] # parent of current switch
			while pre is not None and cur not in done:
				if switch_included[pre] is False:
					dpids[pre]["cost"] = dpids[pre]["cost"]+dpids_cost[pre]["cost"]*2
					if algorithm != "BRANCH_AWARE":
						dpids[pre]["capacity"] = dpids[pre]["capacity"]-2
					switch_included[pre] = True

				if edge_included[cur][pre] is False:
					switches[pre][cur]["cost"] = switches[pre][cur]["cost"] + switches_cost[pre][cur]["cost"]*flow_rate
					switches[cur][pre]["cost"] = switches[cur][pre]["cost"] + switches_cost[cur][pre]["cost"]*flow_rate
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
				pre = sp[src][cur]

			# add destination host
			if dst not in treeports:
				treeports[dst] = set()
			treeports[dst].add(hosts[dh]['port'])

	return treeports

def tree_ports_all(sh, dhs, algorithm, flow_rate, algo_runner_obj):
	global ports
	count = 0
	if(algorithm == "SIMPLE_SPT"):
		ports.clear()
		ports[sh] = tree_ports_simple(sh, dhs, flow_rate)
		print ports[sh]
		algo_runner_obj.show_new_tree(sh, dhs, ports[sh], switches, hosts, dpids, sw_coor, ho_coor)
		count = install_simple_flows()
	elif(algorithm == "MINEDGE_SPT"):
		ports.clear()
		ports[sh] = tree_ports_minedge(sh, dhs, flow_rate)
		print ports[sh]
		algo_runner_obj.show_new_tree(sh, dhs, ports[sh], switches, hosts, dpids, sw_coor, ho_coor)
		count = install_simple_flows()
	elif(algorithm == "BRANCH_AWARE"):
		ports.clear()
		ports[sh] = tree_ports_minedge(sh, dhs, flow_rate)
		print ports[sh]
		algo_runner_obj.show_new_tree(sh, dhs, ports[sh], switches, hosts, dpids, sw_coor, ho_coor)
		count = install_branch_aware_flows(sh, dhs)
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

def install_branch_aware_flows(sh, dhs):
	global switch_usage
	count = 0
	branch_node = {}
	degree = {}
	installed = {}
	branch_node_sw = {}


	src = hosts[sh]['switch']

	for dh in dhs:
		branch_node[dh] = None

	for sw in switches.keys():
		branch_node_sw[sw] = 0

	for dh in dhs:
		dst = hosts[dh]['switch']
		cur = dst
		pre = cur
		first = 1
		while cur is not None :
			if(len(switch_usage[cur])>1):
				if (first is not 1):
					port = switches[cur][pre]["port"]
					branch_node[dh] = cur, port
					break
				elif (first is 1):
					break
			elif(len(switch_usage[cur])==1):
				pre = cur
				cur = sp[src][cur]
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
			if (len(switch_usage[sw])>1):
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
				f.addMatch("in_port", reverse_path_port(hosts[h],sw))
				f.addMatch("dl_type", 0x800)
				f.addMatch("nw_src", hosts[h]['ip'])
				f.addMatch("nw_dst", MCAST_ADDR)
				f.addAction("GROUP", group_id=newgid)
				f.install()
				count += 1
				dpids[sw]["capacity"] = dpids[sw]["capacity"]-1

	for h in ports:
		for dh in dhs:
			if branch_node[dh] is not None:
				sw, p = branch_node[dh]
				if sw is not None:
					f = FlowEntry(dpids[sw]["id"])
					f.addMatch("in_port", reverse_path_port(hosts[h],sw))
					f.addMatch("dl_type", 0x800)
					f.addMatch("nw_dst", MCAST_ADDR)
					f.addAction("SET_FIELD", field="ipv4_dst", value=hosts[dh]['ip'])
					f.addAction("OUTPUT", port = p)
					f.install()
					count += 1
					dpids[sw]["capacity"] = dpids[sw]["capacity"]-1

	for h in ports:
		i = 0
		for sw in ports[h]:
			if(len(switch_usage[sw])==1):
				f = FlowEntry(dpids[sw]["id"])
				f.addMatch("in_port", reverse_path_port(hosts[h],sw))
				f.addMatch("dl_type", 0x800)
				f.addMatch("nw_src", hosts[h]['ip'])
				f.addMatch("nw_dst", hosts[switch_usage[sw][0]]['ip'])
				for p in ports[h][sw]:
					f.addAction("OUTPUT", port = p)
				f.install()
				i += 1

	increment_mcast_addr()
	return count


def install_lq_flows():
	for t in ports_lq: # for each transcoder as source
		for sw in ports_lq[t]: # for each switch in the tree
			# group entry
			newgid = get_next_gid(sw)
			g = GroupEntry(dpids[sw]["id"], newgid, "ALL")
			i = 0
			for p in ports_lq[t][sw]: # for each switch port in the tree
				g.addBucket()
				g.addAction(i, "OUTPUT", port=p)
				i += 1
			g.install()
			# flow entry (also match on in_port for reverse path check)
			# do not install on transcoder switch, tos is not set by T
			if not sw == tees[t]['switch']:
				f = FlowEntry(dpids[sw]["id"])
				f.addMatch("in_port", reverse_path_port(tees[t],sw))
				f.addMatch("dl_type", 0x800)
				f.addMatch("ip_dscp", DSCP_VALUE)
				f.addMatch("nw_src", tees[t]['ip'])
				f.addMatch("nw_dst", MCAST_ADDR)
				f.addAction("GROUP", group_id=newgid)
				f.install()
		# set ip dscp when coming from T
		# the last group added to T's switch refers to the low-capacity tree
		tsw = tees[t]['switch']
		lastgid = gid[tsw]-1
		# flow entry (match on in_port, not nw_src, because original IP address
		# should be kept)
		f = FlowEntry(dpids[tsw]["id"])
		f.addMatch("in_port", tees[t]['port'])
		f.addMatch("dl_type", 0x800)
		f.addMatch("nw_dst", MCAST_ADDR)
		f.addAction("SET_FIELD", field="ip_dscp", value=DSCP_VALUE)
		f.addAction("GROUP", group_id=lastgid)
		f.install()

def dump_sp():
	for s in sp:
		print "sp[%s]:%s" % (s, sp[s])
	print #newline

def dump_ss_trees():
	for sh in hosts: # source host
		src = hosts[sh]['switch'] # source switch
		print "source: %s (%s)" % (sh,src)
		for dh in hosts: # destination hosts
			if dh != sh:
				dst = hosts[dh]['switch'] # destination switch
				print "dest: %s (%s)" % (dh,dst)
				if dh not in low_hosts:
					print "pre[%s]=%s, port=%d" % (dh,dst,hosts[dh]['port'])
				# walk back until root (pre is None)
				cur = dst # current switch
				pre = sp[src][cur] # parent of current switch
				while pre is not None:
					port = switches[pre][cur]["port"]
					print "pre[%s]=%s, port=%d" % (cur,pre,port)
					cur = pre
					pre = sp[src][cur]

		for t in tees: # transcoders (also part of multicast group)
			dst = tees[t]['switch'] # destination switch
			print "dest: %s (%s)" % (t,dst)
			# walk back towards source until root (pre is None)
			cur = dst # current switch
			pre = sp[src][cur] # parent of current switch
			while pre is not None:
				port = switches[pre][cur]["port"]
				print "pre[%s]=%s, port=%d" % (cur,pre,port)
				cur = pre
				pre = sp[src][cur]

		portbuf = "ports:"
		for sw in ports[sh]:
			for port in ports[sh][sw]:
				portbuf += " %s-eth%d" % (sw,port)
		print portbuf
		print #newline

def dump_low_trees():
	for t in tees: # source transcoder
		src = tees[t]['switch'] # source switch
		print "source: %s (%s)" % (t,src)
		for dh in low_hosts: # destination low-capacity hosts
			dst = hosts[dh]['switch'] # destination switch
			print "dest: %s (%s)" % (dh,dst)
			print "pre[%s]=%s, port=%d" % (dh,dst,hosts[dh]['port'])
			# walk back until root (pre is None)
			cur = dst # current switch
			pre = sp[src][cur] # parent of current switch
			while pre is not None:
				port = switches[pre][cur]["port"]
				print "pre[%s]=%s, port=%d" % (cur,pre,port)
				cur = pre
				pre = sp[src][cur]
		portbuf = "ports:"
		for sw in ports_lq[t]:
			for port in ports_lq[t][sw]:
				portbuf += " %s-eth%d" % (sw,port)
		print portbuf
		print #newline

def take_new_hosts():
	global src_host
	global dest_hosts
	src_host = raw_input("Enter the new source host\n")
	dest_hosts = raw_input("Enter the new destination hosts\n")
	print src_host
	print dest_hosts

def menu():

	options = [
		{'str': "Quit", 'action': None},
		{'str': "Dump shortest paths", 'action': dump_sp},
		{'str': "Dump source-specific trees", 'action': dump_ss_trees},
		{'str': "Dump low-capacity trees", 'action': dump_low_trees},
		{'str': "Want to enter new source host or new receivers", 'action': take_new_hosts}
	]

	while True: # until quit
		while True: # while bad input

			for i in range(len(options)):
				print "%d - %s" % (i, options[i]['str'])
			print #newline

			try:
				choice = int(raw_input("Choose an option: "))
				if choice < 0 or choice >= len(options):
					raise ValueError
				break
			except ValueError:
				print "Invalid choice: enter a number between and %d" \
					% (len(options)-1)
			except (EOFError, KeyboardInterrupt):
				print #newline
				choice = 0
				break

		print #newline

		if choice == 0: # quit
			break

		if not options[choice]['action'] is None:
			options[choice]['action']()

def evaluate():
	global switches_cost
	global switches
	global dpids
	global dpids_cost
	link_included = defaultdict(dict)
	for src in switches:
		for dest in switches[src]:
			link_included[src][dest] = False
	print
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

	output = []
	output += [{"avg_link_usage":avg_link_usage}]
	output += [{"avg_switch_usage":avg_switch_usage}]
	output += [{"lowest_link_usage":lowest_link_usage}]
	output += [{"highest_link_usage":highest_link_usage}]
	output += [{"bw_used":bw_used}]
	output += [{"flows_used":flows_used}]
	output += [{"num_links":num_links}]
	output += [{"num_switches":num_switches}]
	#output += [{"MCAST_ADDR":MCAST_ADDR}]
	return output
			
def caller_function(entries, algo_runner_obj):
	global k
	global algorithm
	entry = entries[k][1]
	k += 1
	print k
	source = entry['src_host']
	destination = entry['dest_hosts']
	algorithm1 = entry['algorithm']
	algorithm = algorithm1
	flow_rate = entry['flow_rate']
	shortest_paths_all(flow_rate)
	#print "** Generating port sets for trees **"
	count = tree_ports_all(source, destination, algorithm, flow_rate, algo_runner_obj)
	print source, destination, algorithm, "Number of entries are :", count
	output = evaluate()
	algo_runner_obj.print_specifics(source, destination, algorithm1, output)
	#print "avg_link_usage:",avg_link_usage,"avg_switch_usage:",avg_switch_usage
	print

if __name__ == "__main__":
	filejson = open("../topo/q_fattree_minedge.json")
	#filejson = open("../topo/q_fattree_minedge_one.json")
	topojson = json.load(filejson)
	entries = topojson['entries']
	entries = sorted(entries.items(), key = lambda x: int(x[0]))
	
	src_file = entries[0][1]['src_file']
	load_json_topology("../topo/"+src_file)



	root = Tk()
	algo_runner_obj = algo_runner(root, switches, hosts, dpids, sw_coor, ho_coor)
	button = Button(root, text = "Construce next tree", command = partial(caller_function, entries, algo_runner_obj))
	button.pack()
	#print button
	root.mainloop()
