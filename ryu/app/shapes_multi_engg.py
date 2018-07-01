from Tkinter import *
from collections import defaultdict
from functools import partial
import json
import operator
import copy
import random
tree_no = 0
total_bw_usage = 0
total_flows_usage = 0

class algo_runner:


	def __init__(self, root, switches, hosts, dpids, sw_coor, ho_coor):
		self.root = root
		self.total_canvas_width = 1300
		self.canvas_width = self.total_canvas_width - 300
		self.canvas_height = 700
		canvas = Canvas(self.root, width = self.total_canvas_width, height = self.canvas_height)
		canvas.pack()
		self.canvas = canvas
		self.dpids = {}
		self.initialize(switches, hosts, dpids, sw_coor, ho_coor)

	def initialize(self, switches, hosts, dpids, sw_coor, ho_coor):
		self.dpids = {}
		self.canvas.delete("all")
		self.l0_switches = 0
		self.l1_switches = 0
		self.l2_switches = 0
		self.num_of_hosts = 0
		self.switches = copy.deepcopy(switches)
		for entry in dpids:
			if entry.find("s")!=-1:
				self.dpids[entry] = copy.deepcopy(dpids[entry])
		self.hosts = copy.deepcopy(hosts)
		self.sw_coor = copy.deepcopy(sw_coor)
		self.ho_coor = copy.deepcopy(ho_coor)
		self.port_rel = defaultdict(dict)
		self.fill_port_rel()
		#print (self.port_rel)

		self.find_sw_in_each_level()
		self.fill_sw_coor()
		self.fill_ho_coor()
		self.put_links(hosts)
		self.put_switches(dpids)
		self.put_hosts()

	def print_specifics(self, sh, dhs, bw_usage, flows_usage, highest_till_now):
		global tree_no
		global total_bw_usage
		global total_flows_usage
		tree_no += 1
		total_bw_usage += bw_usage
		total_flows_usage += flows_usage
		index = 100
		lister = []
		lister += [{"tree_no":tree_no}]
		lister += [{"sh":sh}]
		lister += [{"dhs":dhs}]
		lister += [{"bw_usage":bw_usage}]
		lister += [{"flows_usage":flows_usage}]
		lister += [{"total_bw_usage":total_bw_usage}]
		lister += [{"total_flows_usage":total_flows_usage}]
		lister += [{"highest_link_usage_till_now":highest_till_now}]
		for value in lister:
			index += 50
			self.canvas.create_text(self.canvas_width+100,index, text = value.keys()[0]+": %s"%value[value.keys()[0]] , fill = "black")


	def show_new_tree(self, sh, dhs, ports, switches, hosts, dpids, sw_coor, ho_coor):
		self.initialize(switches, hosts, dpids, sw_coor, ho_coor)
		for src in ports:
			all_ports = list(ports[src])
			for port in all_ports:
				dst = self.port_rel[src][port]
				if dst.find("h") == -1:
					x1 = self.sw_coor[src]["x"]
					y1 = self.sw_coor[src]["y"]
					x2 = self.sw_coor[dst]["x"]
					y2 = self.sw_coor[dst]["y"]
				else:
					x1 = self.sw_coor[src]["x"]
					y1 = self.sw_coor[src]["y"]
					x2 = self.ho_coor[dst]["x"]
					y2 = self.ho_coor[dst]["y"]
				self.canvas.create_line(x1, y1, x2, y2, fill = "red", width = 3)

		sw = self.hosts[sh]["switch"]
		x1 = self.sw_coor[sw]["x"]
		y1 = self.sw_coor[sw]["y"]
		x2 = self.ho_coor[sh]["x"]
		y2 = self.ho_coor[sh]["y"]
		self.canvas.create_line(x1, y1, x2, y2, fill = "red", width = 3)

	def show_trees_from_final_trees(self, sh, dhs, switches, hosts, dpids, sw_coor, ho_coor, tree, branch_state_nodes):
		self.initialize(switches, hosts, dpids, sw_coor, ho_coor)
		covered_node = {}
		for src in tree:
			dst = tree[src]
			if dst is not None and src != dst:
				if src.find("h") != -1:
					x1 = self.ho_coor[src]["x"]
					y1 = self.ho_coor[src]["y"]
					x2 = self.sw_coor[dst]["x"]
					y2 = self.sw_coor[dst]["y"]
				elif dst.find("h")!=-1:
					x1 = self.sw_coor[src]["x"]
					y1 = self.sw_coor[src]["y"]
					x2 = self.ho_coor[dst]["x"]
					y2 = self.ho_coor[dst]["y"]
				else:
					x1 = self.sw_coor[src]["x"]
					y1 = self.sw_coor[src]["y"]
					x2 = self.sw_coor[dst]["x"]
					y2 = self.sw_coor[dst]["y"]
				self.canvas.create_line(x1, y1, x2, y2, fill = "red", width = 3)
		for sw in branch_state_nodes:
			self.canvas.create_oval(self.sw_coor[sw]["x"]-30,self.sw_coor[sw]["y"]-30,self.sw_coor[sw]["x"]+30,self.sw_coor[sw]["y"]+30, fill = "red")
			self.canvas.create_text(self.sw_coor[sw]["x"],self.sw_coor[sw]["y"], text = "%s"%sw, fill = "white")
			self.canvas.create_text(self.sw_coor[sw]["x"]-35,self.sw_coor[sw]["y"], text = "%s"%(self.dpids[sw]["cost"]) , fill = "black")

	def fill_port_rel(self):
		for src in self.switches:
			for dst in self.switches[src]:
				self.port_rel[src][self.switches[src][dst]["port"]] = dst

		for host in self.hosts:
			self.port_rel[self.hosts[host]["switch"]][self.hosts[host]["port"]] = host

	def find_sw_in_each_level(self):
		for sw in self.dpids:
			if self.dpids[sw]["level"] == 1:
				self.l0_switches += 1
			elif self.dpids[sw]["level"] == 2:
				self.l1_switches += 1
			elif self.dpids[sw]["level"] == 3:
				self.l2_switches += 1

	def fill_sw_coor(self):
		l0_index = 1
		l1_index = 1
		l2_index = 1

		self.dpids = sorted(self.dpids.items(), key = lambda x: int(str(x[0]).replace("s", "")))
		#print self.dpids
		for item in self.dpids:
			sw = item[0]
			temp = {}
			if item[1]["level"] == 3:
				y = self.canvas_height/5
				x = (self.canvas_width/(self.l2_switches+1))*l2_index
				temp["x"] = x
				temp["y"] = y
				l2_index += 1
				self.sw_coor[sw] = copy.deepcopy(temp)
			if item[1]["level"] == 2:
				y = (self.canvas_height/5)*2
				x = (self.canvas_width/(self.l1_switches+1))*l1_index
				temp["x"] = x
				temp["y"] = y
				l1_index += 1
				self.sw_coor[sw] = copy.deepcopy(temp)
			if item[1]["level"] == 1:
				y = (self.canvas_height/5)*3
				x = (self.canvas_width/(self.l0_switches+1))*l0_index
				temp["x"] = x
				temp["y"] = y
				l0_index += 1
				self.sw_coor[sw] = copy.deepcopy(temp)

	def fill_ho_coor(self): 
		x_index = 0
		self.hosts = sorted(self.hosts.items(), key = lambda x: int(str(x[0]).replace("h", "")))
		for item in self.hosts:
			host = item[0]
			temp = {}
			sw_conn = item[1]["switch"]
			x = self.sw_coor[sw_conn]["x"]
			if x_index == 0:
				temp["x"] = x-50
				x_index += 1
			elif x_index == 1:
				temp["x"] = x-25
				x_index += 1
			elif x_index == 2:
				temp["x"] = x+25
				x_index += 1
			elif x_index == 3:
				temp["x"] = x+50
				x_index = 0
			temp["y"] = (self.canvas_height/5)*4

			self.ho_coor[host] = copy.deepcopy(temp)

	def put_switches(self, dpids):
		self.dpids = {}
		for sw in dpids:
			self.dpids[sw] = copy.deepcopy(dpids[sw])
		for sw in self.sw_coor:
			self.canvas.create_oval(self.sw_coor[sw]["x"]-30,self.sw_coor[sw]["y"]-30,self.sw_coor[sw]["x"]+30,self.sw_coor[sw]["y"]+30, fill = "green")
			self.canvas.create_text(self.sw_coor[sw]["x"],self.sw_coor[sw]["y"], text = "%s"%sw, fill = "white")
			self.canvas.create_text(self.sw_coor[sw]["x"]-35,self.sw_coor[sw]["y"], text = "%s"%(self.dpids[sw]["cost"]) , fill = "black")

	def put_hosts(self):
		for host in self.ho_coor:
			self.canvas.create_rectangle(self.ho_coor[host]["x"]-10,self.ho_coor[host]["y"]-10,
										self.ho_coor[host]["x"]+10,self.ho_coor[host]["y"]+10, fill = "black")
			self.canvas.create_text(self.ho_coor[host]["x"],self.ho_coor[host]["y"], text = "%s"%((self.hosts[host]["ip"]).replace("10.0.0.","")), fill = "white")

	def put_links(self, hosts):
		included = defaultdict(dict)
		self.hosts = copy.deepcopy(hosts)
		for src in self.switches:
			for dst in self.switches[src]:
				included[src][dst] = 0
		for src in self.switches:
			for dst in self.switches[src]:
				if src.find("s")!=-1 and dst.find("s")!=-1:
					if included[dst][src] != 1:
						x1 = self.sw_coor[src]["x"]
						y1 = self.sw_coor[src]["y"]
						x2 = self.sw_coor[dst]["x"]
						y2 = self.sw_coor[dst]["y"]
						self.canvas.create_line(x1, y1, x2, y2, fill = "blue", width = 3)
						if x1 == x2:
							self.canvas.create_text((x1+x2)/2-6,(y1+y2)/2, text = "%s"%(self.switches[src][dst]["cost"]), fill = "black")
						elif x1 > x2 :
							self.canvas.create_text((x1+x2)/2+10,(y1+y2)/2+5, text = "%s"%(self.switches[src][dst]["cost"]), fill = "black")
						else:
							self.canvas.create_text((x1+x2)/2-10,(y1+y2)/2+5, text = "%s"%(self.switches[src][dst]["cost"]), fill = "black")
						included[src][dst] = 1

		for host in self.hosts:
			sw = self.hosts[host]["switch"]
			x1 = self.ho_coor[host]["x"]
			y1 = self.ho_coor[host]["y"]
			x2 = self.sw_coor[sw]["x"]
			y2 = self.sw_coor[sw]["y"]
			self.canvas.create_line(x1, y1, x2, y2, fill = "black")


	def change_fun(self):
		line = self.canvas.create_line(0,0,200,50, fill = "red")
		val = 8
		text = self.canvas.create_text(100,25, text = "%s"%val, fill = "blue")
		circle = self.canvas.create_oval(50,50,75,75, fill = "green")
		self.canvas.create_text(62.5,62.5, text = "%s"%val, fill = "blue")
		circle = self.canvas.create_oval(100,50,125,75, fill = "green")


