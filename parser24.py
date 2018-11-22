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
line_count = 0
current_obj = None
current_obj_type = None
DEBUG = True


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
		
	def add_formals_to_init(self, f):
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
		
		

def throw_error(reason):
	global line_count
	illegal = True
	error_line = line_count
	error_msg = reason + " encountered in line " + str(error_line)

def run(input, output):
	import os
	global line_count
	
	with open(input, 'r') as file:
		line = file.readline()
		while (line):
			line_count += 1
			line = tokenize_line(line)
			line = file.readline()
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
	if DEBUG:
		print("DEBUG: INPUT: " + line)
	current_token = ""
	for c in line:	
		if ord(c) in WHITESPACE:
			if parsing_string:
				current_token += c # TODO anything else?
			elif current_token != "":
				token = current_token
				current_token = ""
				if token.startswith("//"): # comment, skip the rest of line
					current_token = ""
					break
				else:
					add_to_ast(token)
			else:
				pass # just clearing whitespace
		elif is_valid_char(c):
			current_token += c # TODO anything else?
		else:
			throw_error("Forbidden character: " + str(c))
			break
	
	
def add_to_ast(token):
	global expecting
	if DEBUG:
		print("DEBUG: Tokenizing " + token)
	try:
		TOKEN_TO_HANDLER[expecting[0]](token)
	except KeyError as e:
		print("Parser error: No handler for token " + token + " while expecting " + expecting[0])
		exit(1)
	
def handle_protodecs(token):
	global expecting
	if token == "protocol":
		expecting.insert(0, "<protodec>")
		current_obj = Protocol()
		current_obj_type = "Protocol"
		ast.append(current_obj)
	else:
		expecting = expecting[1:] # rest of protodecs is empty
		add_to_ast(token)
		
def handle_classdecs(token):
	global expecting
	if token == "class":
		expecting.insert(0, "<classdec>")
		current_obj = Class()
		current_obj_type = "Class"
		ast.append(current_obj)
	else:
		expecting = expecting[1:] # rest of classdecs is empty
		add_to_ast(token)
		
def handle_protodec(token)
	global expecting
	global current_obj
	if assert_obj_type("Protocol"):
		if current_obj.typeid == None:
			if is_id(token):
				current_obj.set_typeid(token)
			else
				throw_error("Encountered " + token + " while expecting a typeid for a protodec")
		elif # TODO NOW protodec:typevars
	
	
def is_id(token):

def assert_obj_type(t):
	#global current_obj_type
	if t == current_obj_type:
		return True
	else:
		throw_error("Encountered a " + t + " while expecting a " + current_obj_type)
		return False
		
	
# A recursive handler for taking the AST array and formatting it into a string for .ast output
def ast_to_string(ast, out, indent_level):
	if indent_level == 0:
		out += "(program\n"
	indent = indent_level + 1
	
	# TODO redo this section now that I'm using classes
	"""
	for e in ast:
		if hasattr(next, "__len__"): # check if we need to recurse
			out += ast_to_string(e, out, indent)
		else:
			# TODO 
			print("Not sure what to do here, e is not array: " + str(e))
	
		# TODO more here
	"""
	
	out += ")"
	return out
			
			


TOKEN_TO_HANDLER = { 
"<protodecs>" : handle_protodecs,
"<classdecs>" : handle_classdecs,
"<protodec>" : handle_protodec,
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