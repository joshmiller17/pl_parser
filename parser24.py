#! /usr/bin/env python2.7
"""
CS 7400
Quirk 24 Parser
Author: Josh Miller
"""
import traceback
import copy

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



# TODO
#  handlers for:
#    funproto
#    classdec
#    classbody
#    constdec
#    globaldec
#    fielddec
#    formal
#    fundec
#    block
#    localdec
#    vardec
#    type
#    primtype
#    rtype
#    arrow
#    stm
#    exp
#    lhs
#    disjunct
#    conjunct
#    simple
#    term
#    factor
#    factor-rest
#    floatliteral -- ignore for now, handle later
#    exponent  -- ignore for now, handle later



class Protocol:

	def __init__(self):
		self.typeid = None
		self.extends = []
		self.typevars = []
		self.funprotos = []
		self.expecting_more_vars = False
		
	def set_typeid(self, i):
		self.typeid = i
		
	def add_typevar(self, v):
		self.typevars.append(v)
		
	def set_expecting(self, b):
		self.expecting_more_vars = b
		
	# must be a typeapp
	def add_extends(self, t):
		self.extends.append(t)
		
	def add_funproto(self, f):
		self.funprotos.append(f)
		
	def __str__(self):
		return "<Protocol; id=" + str(self.typeid) + ", extends=" \
			+ str(self.extends) + ", typevars=" + str(self.typevars) \
			+ ",funprotos=" + str(self.funprotos) + ",expecting more?=" \
			+ str(self.expecting_more_vars) + ">"

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
		
		

def throw_error(reason, addl=""):
	global line_count
	global illegal
	global error_msg
	if illegal and error_msg: # already have an error
		return
	illegal = True
	error_line = line_count
	error_msg = reason + " in line " + str(error_line)
	if addl:
		error_msg += "\n" + addl
	if DEBUG:
		print("Traceback:")
		print(traceback.extract_stack())

def run(input, output):
	import os
	global line_count
	global illegal
	
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
		print("Encountered syntax error while parsing " + str(input) + ":")
		print(error_msg)
		if DEBUG: # addl debug info
			print("Expecting: " + str(expecting))
			print("Current object type: " + str(current_obj_type))
			print("Current object: " + str(current_obj))
			

def is_valid_char(c, mustbe=[], cantbe=[]):
	restrictions = copy.copy(cantbe)
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
	
def is_id(token):
	valid = is_valid_char(token[0], mustbe=["lower"])
	if len(token) > 1:
		for c in token[1:]:
			valid = valid and is_valid_char(c, cantbe=["print"]) # subsequent
	return valid
	
def is_tvar(token):
	valid = is_valid_char(token[0], mustbe=["upper"])
	if len(token) > 1:
		for c in token[1:]:
			valid = valid and is_valid_char(c, cantbe=["print"]) # subsequent
	return valid
	
def is_intliteral(token):
	valid = is_valid_char(token[0], mustbe["digit"])
	if len(token) > 1:
		for c in token[1:]:
			valid = valid and is_valid_char(c, mustbe=["digit"])
	return valid
	
def is_stringliteral(token):
	str = token[1:-1]
	if not token.startswith("\"") or not token.endswith("\""):
		return False
	valid = True
	for c in str:
		valid = valid and is_valid_char(c)
	return valid
		
def is_charliteral(token):
	return len(token) == 3 and token[0] == "\'" and token[2] == "\'" \
		and is_valid_char(token[1])
		
def is_floatliteral(token):
	return False # TODO
		
def is_literal(token):
	if token == "null":
		return True
	elif token == "true":
		return True
	elif token == "false":
		return True
	else:
		return is_charliteral(token) or is_stringliteral(token) \
				or is_intliteral(token) or is_floatliteral(token)
	
			
def tokenize_line(line):
	if DEBUG and not illegal:
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
			throw_error("Forbidden character: \'" + str(c) + "\'")
			break
	
# Find the handler to the token, a handler handler
def add_to_ast(token):
	global expecting
	if illegal:
		return
	if DEBUG:
		print("DEBUG: Tokenizing <" + token + "> while expecting " + expecting[0])
	try:
		handler = TOKEN_TO_HANDLER[expecting[0]]
		handler(token)
		if DEBUG:
			print("Token <" + token + "> sent to " + str(handler))
	except KeyError as e:
		print("Parser error: No handler for token " + token + " while expecting " + expecting[0])
		exit(1)
	
def handle_protodecs(token):
	global expecting
	global current_obj
	global current_obj_type
	if token == "protocol":
		expecting.insert(0, "<protodec>")
		current_obj = Protocol()
		current_obj_type = "Protocol"
		ast.append(current_obj)
	else:
		expecting = expecting[1:] # rest of protodecs is empty
		add_to_ast(token) # find a new handler
		
def handle_classdecs(token):
	global expecting
	if token == "class":
		expecting.insert(0, "<classdec>")
		current_obj = Class()
		current_obj_type = "Class"
		ast.append(current_obj)
	else:
		expecting = expecting[1:] # rest of classdecs is empty
		add_to_ast(token) # find a new handler
		
def handle_classdec(token):
	global expecting
	pass # TODO, see protodec for guide
	throw_error("Parser not defined for this operation.")
	
def handle_funprotos(token):
	global expecting
	if token == "fun":
		expecting.insert(0, "<funproto>")
		current_obj = Funproto()
		current_obj_type = "Funproto"
		ast.append(current_obj)
	else:
		expecting = expecting[1:] # rest of funprotos is empty
		add_to_ast(token) # find a new handler
	
def handle_funproto(token):
	global expecting
	pass # TODO, see protodec for guide
	throw_error("Parser not defined for this operation.")
		
def handle_protodec(token):
	# TODO think through this logic, check to make sure it works
	global expecting
	global current_obj
	if assert_obj_type("Protocol"):
		# expect id first
		if current_obj.typeid == None:
			if is_id(token):
				current_obj.set_typeid(token)
			else:
				throw_error("Encountered " + token + " while expecting a typeid for a protodec")
		# tvars next, can be empty or Tvar or Tvar, Tvar, ... Tvar
		elif ',' == token: # expect another tvar
			if current_obj.expecting_more_vars:
				throw_error("Syntax error", addl="Too many commas in typevars?")
			current_obj.set_expecting(True)
		elif ',' in token: # comma is part of another token
			for raw_token in token.split(','):
				t = raw_token.strip() # double check no whitespace
				add_to_ast(t)
				add_to_ast(',') # splitting on commas, put commas back
		elif is_tvar(token): # no comma
			current_obj.add_typevar(token)
			current_obj.set_expecting(False)
		elif token == "extends":
			if current_obj.expecting_more_vars:
				throw_error("Syntax error", addl="Expecting another typevar")
			else:
				expecting.insert(0, "<extends>")
		elif '{' in token:
			if current_obj.expecting_more_vars:
				throw_error("Syntax error", addl="Expecting another typevar")
			else:
				if '{' == token:
					expecting = expecting[1:] # rest of protodec is just funprotos
					expecting.insert(0, "<funprotos>")
				else:
					for raw_token in token.split('{'):
						t = raw_token.strip()
						add_to_ast(t) # let handler handler handle it
		else:
			throw_error("Encountered " + token + " while parsing a " + str(current_obj_type))
	else:
		throw_error("Encountered " + token + " while parsing a " + str(current_obj_type))
	print(str(current_obj))
		
def assert_obj_type(t):
	#global current_obj_type
	if t == current_obj_type:
		return True
	else:
		throw_error("Encountered a " + t + " while expecting a " + str(current_obj_type))
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
"<protodec>" : handle_protodec,
"<classdecs>" : handle_classdecs,
"<classdec>" : handle_classdec,
"<funprotos>" : handle_funprotos,
"<funproto>" : handle_funproto,
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