#! /usr/bin/env python2.7
"""
CS 7400
Quirk 24 Parser
Author: Josh Miller
"""

SPACE = 0x20
LF = 0xa
CR = 0xd
WHITESPACE = [ SPACE, LF, CR ]
COMMENT = "//" # followed by LF or CR
ASSIGNOP = "="
OROP = "||"
ANDOP = "&&"
RELOPS = ["==", "!=", "<", "<=", ">", ">="]
ADDOPS = ["+", "-"]
MULOPS = ["*", "/"]
UNOPS = ["!", "-"]
PRINTABLES = [" ", "!", "#", "$", "%", "&", "(", ")", "*", \
       "+", ",", "-", ".", "/", ":", ";", "<", "=", ">", "?", "@", "[", "]", "^", "{", "}", "~"]
illegal = False
error_line = 0
error_msg = ""
parsing_string = False
expecting = ["<protodecs>", "<classdecs>", "<stm>"] #initial syntax expectations
ast = []
current_obj = None
current_obj_type = None


class Protocol:

	def __init__(self):
		self.typeid = None
		self.extends = []
		self.typevars = []
		self.funprotos = []
		
	def set_typeid(self, i):
		self.typeid = i
		
	def add_typevar(self, v):
		self.typevars.append(v)
		
	# must be a typeapp
	def add_extends(self, t):
		self.extends.append(t)
		
	def add_funproto(self, f):
		self.funprotos.append(f)

class Funproto:

	def __init__(self):
		self.id = None
		self.rtype = None
		self.typevars = []
		self.funprotos = []
		
	def set_id(self, i):
		self.id = i
		
	def add_typevar(self, v):
		self.typevars.append(v)

	def add_formals(self, f):
		self.formals.append(f)
		
	def set_rtype(self, r):
		self.rtype = r
		
class Class:
	
	def __init__(self):
		self.id = None
		self.implements = []
		self.typevars = []
		self.funprotos = []
		self.init_formals = []
		self.block = None
		
	def set_id(self, i):
		self.id = i
		
	# must be a typeapp
	def add_implements(self, t):
		self.implements.append(t)
		
	def add_typevar(self, v):
		self.typevars.append(v)
		
	def add_formals_to_init(self, f)
		self.init_formals.append(f)
		
	def add_block(self, b):
		self.block = b
		
class Block:
	
	def __init__(self):
		self.local_decs = []
		self.stms = []
		
	def add_localdec(self, l):
		self.local_decs.append(l)
		
	def add_stm(self, s):
		self.stms.append(s)
		
		

def throw_error(line, reason)
	illegal = True
	error_line = line_count
	error_msg = reason + " encountered in line " + str(error_line)

def run(input, output):
	import os
	line_count = 0
	
	with open(input, 'r') as file:
		line_count += 1
		line = file.readline()
		line = tokenize_line(line)
		# TODO more here
		
		
	with open(output, 'w') as file:
		if illegal:
			file.write("(illegal)")
		else:
			file.write(ast_to_string(ast, "", 0))

	
	if illegal:
		print("Encountered syntax error while parsing " + str(input))
		print(error_msg)
			

def is_valid_char(c, mustbe=[], cantbe=[]):
	restrictions = cantbe
	if mustbe != []:
		options = ["digit", "lower", "upper", "_", "print"]
		for opt in options:
			if opt not in mustbe:
				restrictions.append(opt)
	if c.isdigit() and "digit" not in restrictions:
		return True
	if c.isalpha():
		if c.islower() and "lower" not in restrictions:
			return True
		elif c.isupper() and "upper" not in restrictions:
			return True
	if c == "_" and "_" not in restrictions:
		return True
	if c in PRINTABLES and "print" not in restrictions:
		return True
	return False
			
def tokenize_line(line):
	for c in line:
		current_token = ""
		if c in WHITESPACE:
			if parsing_string:
				current_token += c # TODO anything else?
			elif current_token != "":
				token = current_token
				current_token = ""
				add_to_ast(token)
			else:
				pass # just clearing whitespace
		elif is_valid_char(c):
			current_token += c # TODO anything else?
		else:
			throw_error(line_count, "Forbidden character: " + str(c))
			break
	
	
def add_to_ast(token):
	try:
		TOKEN_TO_HANDLER[expecting[0]](token)
	except KeyError as e:
		print("Parser error: No handler for token " + token + " while expecting " + expecting[0])
	
def handle_protodecs(token):
	if token == "protocol":
		expecting.insert(0, "<protodec>")
		current_obj = Protocol()
		current_obj_type = "Protocol"
		ast.append(current_obj)
	else:
		expecting = expecting[1:] # rest of protodecs is empty
		add_to_ast(token)
		
def handle_classdecs(token):
	if token == "class":
		expecting.insert(0, "<classdec>")
		current_obj = Class()
		current_obj_type = "Class"
		ast.append(current_obj)
	else:
		expecting = expecting[1:] # rest of classdecs is empty
		add_to_ast(token)
	
# A recursive handler for taking the AST array and formatting it into a string for .ast output
def ast_to_string(ast, out, indent_level):
	if indent_level == 0:
		out.append("(program\n")
	indent = indent_level + 1
	for e in ast:
		if hasattr(next, "__len__") # check if we need to recurse
			out.append(ast_to_string(e, out, indent))
		else:
			# TODO 
			print("Not sure what to do here, e is not array: " + e)
	
		# TODO more here
	
	out.append(")")
	return out
			
			


TOKEN_TO_HANDLER = { 
"<protodecs>" : handle_protodecs,
"<classdecs>" : handle_classdecs
}			
			
def main():
	import argparse
	prog_desc = "Quirk 24 parser by Josh Miller"
	parser = argparse.ArgumentParser(description=prog_desc)
	parser.add_argument('input', help="Input file name")
	parser.add_argument('output', help="Output file name")
	args = parser.parse_args()
	run(args.input, args.output)
	

if '__main__' == __name__:
	main()