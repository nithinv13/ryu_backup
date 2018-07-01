from collections import defaultdict
import numpy
import copy

class evaluator:

	def __init__(self, switches, hosts, dpids):
		self.switches = switches
		self.hosts = hosts
		self.dpids = dpids

	def save_final_trees(self, final_trees, final_trees_temp):
		for val in final_trees_temp:
			final_trees[val["tree_no"]]["tree_no"] = val["tree_no"]
			final_trees[val["tree_no"]]["tree"] = val["tree"]
			final_trees[val["tree_no"]]["branch_state_nodes"] = val["branch_state_nodes"]
			final_trees[val["tree_no"]]["sh"] = val["sh"]
			final_trees[val["tree_no"]]["dhs"] = val["dhs"]
			final_trees[val["tree_no"]]["flow_rate"] = val["flow_rate"]
			if "switches" in val:
				final_trees[val["tree_no"]]["switches"] = val["switches"]
				final_trees[val["tree_no"]]["dpids"] = val["dpids"]

	def cal_bw_usage_for_single_tree(self, sh, dhs, tree, branch_state_nodes, flow_rate, src_switch, dest_switches, used):
		#print "calculating bw for tree:" + str(id(tree))
		hosts = self.hosts
		#print dest_switches
		next_dest_switches = set()
		bw_used = 0
		for sw in dest_switches:

			cond = 0

			if sw == dest_switches[0]:
				next_dest_switches.clear()

			for switch in used:
				if sw == switch:
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
			while pre != None and pre not in branch_state_nodes and pre != src_switch:
				#bw_used += flow_rate
				bw_used += flow_rate
				cur = pre
				pre = tree[cur]
			if pre in branch_state_nodes:
				next_dest_switches.add(pre)
				#bw_used += flow_rate
				bw_used += flow_rate
			elif pre == src_switch:
				#bw_used += flow_rate
				bw_used += flow_rate
			elif pre == None:
				bw_used += 0

			if sw == dest_switches[len(dest_switches)-1]:
				dest_switches = list(copy.deepcopy(next_dest_switches))
				break

		if len(dest_switches)>0:
			bw_used = bw_used + self.cal_bw_usage_for_single_tree(sh, dhs, tree, branch_state_nodes, flow_rate, src_switch, dest_switches, used)

		return bw_used


	def cal_bw_usage_from_final_trees(self, final_trees):
		bw_usages_all_trees = {}
		for entry in final_trees:
			used = []
			tree_no = final_trees[entry]["tree_no"]
			tree = final_trees[entry]["tree"]
			sh = final_trees[entry]["sh"]
			dhs = final_trees[entry]["dhs"]
			flow_rate = final_trees[entry]["flow_rate"]
			branch_state_nodes = final_trees[entry]["branch_state_nodes"]
			bw_usages_all_trees[tree_no] = self.cal_bw_usage_for_single_tree(sh, dhs, tree, branch_state_nodes, flow_rate, sh, dhs, used)
		return bw_usages_all_trees


	def cal_flows_usage_from_final_trees(self, final_trees):
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

	def cal_highest_link_usage(self, final_trees):
		switches = self.switches
		highest_bw_usage = {}
		lowest_bw_usage = {}
		highest_link_usage = defaultdict(dict)
		for src in switches:
			for dest in switches[src]:
				#print src + "-" + dest
				highest_link_usage[src][dest] = 0
				highest_link_usage[dest][src] = 0
		#print 
		for entry in final_trees:
			tree_no = final_trees[entry]["tree_no"]
			tree = final_trees[entry]["tree"]
			sh = final_trees[entry]["sh"]
			dhs = final_trees[entry]["dhs"]
			flow_rate = final_trees[entry]["flow_rate"]
			for src in tree:
				dest = tree[src]
				if src != dest and dest != None:
					#print src + "-" + dest
					highest_link_usage[src][dest] += flow_rate
					highest_link_usage[dest][src] += flow_rate
			result = 0
			for src in switches:
				for dest in switches[src]:
					if highest_link_usage[src][dest] > result:
						result = highest_link_usage[src][dest]
			highest_bw_usage[tree_no] = result
			result = 10000
			for src in switches:
				for dest in switches[src]:
					if highest_link_usage[src][dest] != 0 and highest_link_usage[src][dest] < result:
						result = highest_link_usage[src][dest]
			lowest_bw_usage[tree_no] = result

		return highest_bw_usage

	def cal_average_link_usage(self, final_trees):
		included = defaultdict(dict)
		switches = self.switches
		for src in switches:
			for dest in switches[src]:
				included[src][dest] = False
		average_link_usage = defaultdict(dict)
		bw_std_deviation = {}
		average_bw_usage = {}
		zero_usage_links_percent = {}
		overly_used_links_percent = {}
		for src in switches:
			for dest in switches[src]:
				average_link_usage[src][dest] = 0
				average_link_usage[dest][src] = 0
		for entry in final_trees:
			values = []
			tree_no = final_trees[entry]["tree_no"]
			tree = final_trees[entry]["tree"]
			sh = final_trees[entry]["sh"]
			dhs = final_trees[entry]["dhs"]
			flow_rate = final_trees[entry]["flow_rate"]
			for src in tree:
				dest = tree[src]
				if src != dest and dest != None:
					#print src + "-" + dest
					average_link_usage[src][dest] += flow_rate
					average_link_usage[dest][src] += flow_rate
			overly_used_links = 0
			links_used = 0
			total_links = 0
			for src in switches:
				for dest in switches[src]:
					total_links += 1
					if average_link_usage[src][dest] > 0:
						links_used += 1
					if average_link_usage[src][dest] > switches[src][dest]["capacity"]:
						overly_used_links += 1
					if included[dest][src] is False:
						included[src][dest] = True
						values += [average_link_usage[src][dest]]
			bw_std_deviation[tree_no] = self.cal_std_deviation(values)
			total_flow = 0
			for src in switches:
				for dest in switches[src]:
					if average_link_usage[src][dest] > 0:
						total_flow += average_link_usage[src][dest]
			result = 0.0
			#result = total_flow/links_used
			result = total_flow/total_links
			average_bw_usage[tree_no] = result

			zero_usage_links_percent[tree_no] = ((float(total_links-links_used))/total_links)*100
			overly_used_links_percent[tree_no] = ((float(overly_used_links))/total_links)*100

		return average_bw_usage, bw_std_deviation, zero_usage_links_percent, overly_used_links_percent

	def cal_avg_number_of_multicast_flows(self, final_trees):
		per_sw_flows_usage = {}
		dpids = self.dpids
		num_of_switches = 0
		for sw in dpids:
			if sw.find("s")!=-1:
				num_of_switches += 1
		for sw in dpids:
			per_sw_flows_usage[sw] = 0
		avg_no_of_multicast_flows = {}
		branch_state_switches = set()
		flows_std_deviation = {}
		zero_usage_switch_percent = {}
		flows_used = 0
		for entry in final_trees:
			values = []
			branch_state_nodes = final_trees[entry]["branch_state_nodes"]
			flows_used += len(branch_state_nodes)
			for sw in branch_state_nodes:
				branch_state_switches.add(sw)
				per_sw_flows_usage[sw] += 1
			result = 0.0
			result = flows_used/num_of_switches
			avg_no_of_multicast_flows[entry] = result

			switches_used = 0
			switches_used_std = 0
			for sw in per_sw_flows_usage:
				if sw.find("s")!=-1:
					if per_sw_flows_usage[sw] >= 0:
						switches_used += 1
						values += [per_sw_flows_usage[sw]]
					if per_sw_flows_usage[sw] > 0:
						switches_used_std += 1
			flows_std_deviation[entry] = self.cal_std_deviation(values)

			zero_usage_switch_percent[entry] = (float(num_of_switches-switches_used_std)/num_of_switches)*100
		return avg_no_of_multicast_flows, flows_std_deviation, zero_usage_switch_percent

	def cal_std_deviation(self, values):
		return numpy.std(values)
		
	def evaluate(self, final_trees, file_name):
		bw_usages_all_trees = self.cal_bw_usage_from_final_trees(final_trees)
		flows_usage = self.cal_flows_usage_from_final_trees(final_trees)
		average_bw_usage, bw_std_deviation , zero_usage_links_percent, overly_used_links_percent = self.cal_average_link_usage(final_trees)
		average_flows_usage, flows_std_deviation, zero_usage_switch_percent = self.cal_avg_number_of_multicast_flows(final_trees)
		#for entry in bw_usages_all_trees:
		#		 str(entry) + ":" + str(bw_usages_all_trees[entry])
		#for entry in flows_usage:
		#	print str(entry) + ":" + str(flows_usage[entry])
		highest_bw_usage = self.cal_highest_link_usage(final_trees)
		for tree_no in final_trees:
			final_trees[tree_no]["bw_usage"] = bw_usages_all_trees[tree_no]
			final_trees[tree_no]["flows_usage"] = flows_usage[tree_no]
			final_trees[tree_no]["highest_link_usage_till_now"] = highest_bw_usage[tree_no]
		X_list = []
		Highest_link_usage = []
		Average_link_usage = []
		Average_flows_usage = []
		Zero_usage_links_percent = []
		Zero_usage_switch_percent = []
		Overly_used_links_percent = []
		Bw_std_deviation = []
		Flows_std_deviation = []
		Total_traffic = []
		Total_flows = []
		total_traffic = 0
		total_flows = 0
		for entry in final_trees:
			X_list += [final_trees[entry]["tree_no"]]
			Highest_link_usage += [highest_bw_usage[final_trees[entry]["tree_no"]]]
			Average_link_usage += [average_bw_usage[final_trees[entry]["tree_no"]]]
			Average_flows_usage += [average_flows_usage[final_trees[entry]["tree_no"]]]
			Zero_usage_links_percent += [zero_usage_links_percent[final_trees[entry]["tree_no"]]]
			Zero_usage_switch_percent += [zero_usage_switch_percent[final_trees[entry]["tree_no"]]]
			Overly_used_links_percent += [overly_used_links_percent[final_trees[entry]["tree_no"]]]
			Bw_std_deviation += [bw_std_deviation[final_trees[entry]["tree_no"]]]
			Flows_std_deviation += [flows_std_deviation[final_trees[entry]["tree_no"]]]
			total_traffic += bw_usages_all_trees[final_trees[entry]["tree_no"]]
			Total_traffic += [total_traffic]
			total_flows += flows_usage[final_trees[entry]["tree_no"]]
			Total_flows += [total_flows]
		fw = open("/home/nithin/c/main_results/"+file_name+".json","w")
		fw.write('{\n\"X_list\":"%s",\n'%X_list)
		fw.write('\"Highest_link_usage\":"%s",\n'%Highest_link_usage)
		fw.write('\"Average_link_usage\":"%s",\n'%Average_link_usage)
		fw.write('\"Bw_std_deviation\":"%s",\n'%Bw_std_deviation)
		fw.write('\"Flows_std_deviation\":"%s",\n'%Flows_std_deviation)
		fw.write('\"Average_flows_usage\":"%s",\n'%Average_flows_usage)
		fw.write('\"Total_traffic\":"%s",\n'%Total_traffic)
		fw.write('\"Total_flows\":"%s",\n'%Total_flows)
		fw.write('\"Zero_usage_links_percent\":"%s",\n'%Zero_usage_links_percent)
		fw.write('\"Zero_usage_switch_percent\":"%s",\n'%Zero_usage_switch_percent)
		fw.write('\"Overly_used_links_percent\":"%s"\n}'%Overly_used_links_percent)
