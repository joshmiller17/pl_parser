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
ARROW = "->"
PRIMTYPES = ["bool", "char", "string", "int", "float"]
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
STM_REDIRECTS = {";" : "<stm-empty>", "if" : "<stm-if>", \
			"while" : "<stm-while>", "for" : "<stm-for>", \
			"return" : "<stm-ret>", "{" : "<block>", \
			"halt" : "<stm-halt>"}
RESERVED = ["if", "while", "for", "return", "halt", "bool", "char", "string", "int", "float"]
illegal = False
error_line = 0
error_msg = ""
parsing_string = False
expecting = ["<protodecs>", "<classdecs>", "<stm>"] #initial syntax expectations
ast = []
line_count = 0
current_obj = None
current_obj_type = None
object_stack = [None]
object_type_stack = ["None"]
DEBUG_LEVEL = 2



# TODO

# EXPRESSIONS
#    factor, factor-rest, etc
#    simple is (term (addop simple)*) -- any terms joined by addops
#    term: a term is a (factor (mulop factor)*) -- any factors joined by mulops
#    disjunct is (conjunct (andop disjunct)*) -- any conjuncts joined by andop
#    conjunct is (simple (relop simple)*) -- any simples joined by relops
#    lhs is (disjunct (orop lhs)*) -- any disjuncts joined by orops
#    exp is lhs (assignop exp)*


#    floatliteral
#    exponent



# TODO tricky to handle "int []" without some kind of lookahead function

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
		self.formals = []
		self.expecting_more_vars = False
		
	def set_id(self, i):
		self.id = i
		
	def add_typevar(self, v):
		self.typevars.append(v)

	def add_formal(self, f):
		self.formals.append(f)
		
	def set_expecting(self, b):
		self.expecting_more_vars = b
		
	def set_rtype(self, r):
		self.rtype = r
		
	def __str__(self):
		return "<Funproto; id=" + str(self.id) + ", rtype=" \
			+ str(self.rtype) + ", typevars=" + str(self.typevars) \
			+ ",formals=" + str(self.formals) + ",expecting more?=" \
			+ str(self.expecting_more_vars) + ">"
		

class Fundec:

	def __init__(self):
		self.id = None
		self.rtype = None
		self.typevars = []
		self.formals = []
		self.block = None
		self.expecting_more_vars = False
		
	def set_id(self, i):
		self.id = i
		
	def add_typevar(self, v):
		self.typevars.append(v)
		
	def set_block(self, b):
		self.block = b

	def add_formal(self, f):
		self.formals.append(f)
		
	def set_expecting(self, b):
		self.expecting_more_vars = b
		
	def set_rtype(self, r):
		self.rtype = r
		
	def __str__(self):
		return "<Fundec; id=" + str(self.id) + ", rtype=" \
			+ str(self.rtype) + ", typevars=" + str(self.typevars) \
			+ ",formals=" + str(self.formals) + ",expecting more?=" \
			+ str(self.expecting_more_vars) + ", block=" + str(self.block) + ">"
		
class Formal:
	
	def __init__(self):
		self.type = None
		self.id = None
		
	def set_type(self, t):
		self.type = t
		
	def set_id(self, i):
		self.id = i
		
class Class:
	
	def __init__(self):
		self.id = None
		self.implements = []
		self.typevars = []
		self.funprotos = []
		self.init_formals = []
		self.block = None
		self.expecting_more_vars = False
		self.expecting_formals = True
		self.bodydecs = []
		
	def set_id(self, i):
		self.id = i
		
	# must be a typeapp
	def add_implements(self, t):
		self.implements.append(t)
		
	def add_typevar(self, v):
		self.typevars.append(v)
		
	def set_expecting(self, b):
		self.expecting_more_vars = b
		
	def found_formals(self):
		self.expecting_formals = False
		
	def add_formal(self, f):
		self.init_formals.append(f)
		
	def add_block(self, b):
		self.block = b
		
	def add_bodydec(self, b):
		self.bodydecs.append(b)
		
class Block:
	
	def __init__(self):
		self.local_decs = []
		self.stms = []
		self.dec_phase = True
		
	def add_localdec(self, l):
		self.local_decs.append(l)
		
	def end_decs(self):
		self.dec_phase = False
		
	def add_stm(self, s):
		self.stms.append(s)
		
class Dec:

	def __init__(self):
		self.type = None
		self.id = None
		self.lit = None
		self.eq = False
		self.dectype = None
		
	def set_type(self, t):
		self.type = t
		
	def set_id(self, i):
		self.id = i
		
	def consume_eq():
		self.eq = True
		
	def set_lit(self, l):
		self.lit = l
		
class Constdec(Dec):

	def __init__(self):
		Dec.__init__(self)
		self.dectype = "const"
		
class Globaldec(Dec):

	def __init__(self):
		Dec.__init__(self)
		self.dectype = "global"
	
class Fielddec:

	def __init__(self):
		self.type = None
		self.id = None
		
	def set_type(self, t):
		self.type = t
		
	def set_id(self, i):
		self.id = i

def stacktrace():
	if DEBUG_LEVEL > 0.5:
		print("\nDEBUG: Error traceback:")
		for l in traceback.extract_stack()[1:-1]:
			print("------ " + str(l))
		print("Expecting: " + str(expecting))
		print("Current object type: " + str(current_obj_type))
		print("Current object: " + str(current_obj))
		
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
	stacktrace()

			
# TODO
#def token_lookahead():
	
			
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
		print("\nEncountered syntax error while parsing " + str(input) + ":")
		print(error_msg)
			

def tokenize_line(line, repeat=False):
	if DEBUG_LEVEL > 0 and not illegal and not repeat:
		print("DEBUG: INPUT (line " + str(line_count) + "): " + line[:-1])
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
	if current_token and not current_token.startswith("//"):
		add_to_ast(current_token)
	
# if current obj handling is None, pop from stack
def check_current_obj():
	global current_obj
	global current_obj_type
	global object_stack
	global object_stack_type
	if current_obj == None:
		if object_stack[0] != None:
			# pop object stack
			current_obj = object_stack[0]
			current_obj_type = object_type_stack[0]
			object_stack = object_stack[1:]
			object_stack_type = object_stack_type[1:]
			if DEBUG_LEVEL > 0:
				print("Object stack popped. Current obj = " + current_obj_type)
				print("Remaining obj stack = " + str(object_stack_type))
	
# Find the handler to the token, a handler handler
def add_to_ast(token):
	global expecting
	if illegal:
		return
	if DEBUG_LEVEL > 1:
		print("DEBUG: Tokenizing <" + token + "> while expecting " + expecting[0])
	
	check_current_obj()
	
	try:
		handler = TOKEN_TO_HANDLER[expecting[0]]	
		if DEBUG_LEVEL > 1:
			print("DEBUG: Token <" + token + "> sent to " + str(handler))	
		handler(token)
	except KeyError as e:
		print("\nParser error: No handler for token " + token + " while expecting " + expecting[0])
		stacktrace()
		exit(1)

# handle tokens that have less whitespace than we hope for, such as (int) or :void
# puts space between all special characters
def read_tight_code(token):
	tight_tokens = ['(', ')', '{', '}', ',', ':', ';']
	new_line = token
	for t in tight_tokens:
		new_line = new_line.replace(t, " " + t + " ")
	if DEBUG_LEVEL > 1:
		print("DEBUG: \'" + token + "\' loosened to \'" + new_line + "\'")
	tokenize_line(new_line, repeat=True)
		
		
	
def assert_obj_type(t):
	#global current_obj_type
	if t == current_obj_type:
		return True
	else:
		throw_error("Parser Error: Encountered a " + t + " while expecting object of type " + str(current_obj_type))
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
			

		
def handle_protodecs(token):
	global expecting
	global current_obj
	global current_obj_type
	if token == "protocol":
		expecting.insert(0, "<protodec>")
		if current_obj:
			push_stack()
		current_obj = Protocol()
		current_obj_type = "Protocol"
		ast.append(current_obj) # TODO fix?
	else:
		# no more protodecs, find a new handler
		expecting = expecting[1:]
		add_to_ast(token)

def handle_rtype(token):
	global expecting
	if ':' in token or ')' in token or ';' in token:
		read_tight_code(token)
	elif not is_rtype(token):
		throw_error("Encountered " + token + " while expecting <rtype>")
	else:
		current_obj.set_rtype(token)
		expecting = expecting[1:] # rtype finished
	
def handle_formals(token):
	global expecting
	global current_obj
	global current_obj_type
	
	if ')' in token:
		if ')' is token:
			if expecting[0] == "<formals-rest>":
				throw_error("Expecting another <formal>")
			expecting = expecting[1:] # rest of formals is empty
		else:
			read_tight_code(token)
	
	elif ',' in token:
		if ',' is token:
			expecting.insert(0, "<formals-rest>") # expect another formal
		else:
			read_tight_code(token)		
	elif is_type(token):
		if current_obj_type == "Formal":
			throw_error("Encountered type " + token \
				+ " while parsing a <formal> that already had a type " + str(current_obj.type))
		else:
			if expecting[0] == "<formals-rest>":
				expecting[0] = "<formal>"
			else:
				expecting.insert(0, "<formal>")
			if current_obj:
				push_stack()
			current_obj = Formal()
			current_obj_type = "Formal"
			ast.append(current_obj) # TODO fix?
			current_obj.set_type(token)
	else:
		throw_error("Encountered " + token + " while expecting a <type> for a <formal>")
			
def handle_formal(token):
	global expecting
	global current_obj
	global current_obj_type
	assert_obj_type("Formal")
	
	if not is_id(token):
		if ')' in token:
			read_tight_code(token)
		elif ',' in token:
			if ',' is token:
				throw_error("Encountered " + token + " while expecting an <id>")
			else:
				read_tight_code(token)
		else:
			throw_error("Encountered " + token + " while expecting an <id>")
	else:
		current_obj.set_id(token)
		# add formal to its parent object
		formal_obj = current_obj
		pop_stack()
		current_obj.add_formal(formal_obj)
		expecting = expecting[1:] # formal finished

		
def handle_protodec(token):
	global expecting
	global current_obj
	global current_obj_type
	if assert_obj_type("Protocol"):
		# expect id first
		if current_obj.typeid == None:
			if is_id(token):
				current_obj.set_typeid(token)
			else:
				throw_error("Encountered " + token + " while expecting a typeid for a <protodec>")
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
				expecting.insert(0, "<extends-rest>")
		elif '{' in token:
			if current_obj.expecting_more_vars:
				throw_error("Syntax error", addl="Expecting another typevar")
			else:
				if '{' == token:
					expecting.insert(0, "<funprotos>")
				else:
					throw_error("Syntax error while parsing a <protodec>")
		elif '}' in token:
			if '}' is token:
				expecting = expecting[1:]
			else:
				read_tight_code(token)
		else:
			throw_error("Encountered " + token + " while parsing a " + str(current_obj_type))
	else:
		throw_error("Protocol expected")

		
def handle_classdecs(token):
	global expecting
	global current_obj
	global current_obj_type
	if token == "class":
		expecting.insert(0, "<classdec>")
		if current_obj:
			push_stack()
		current_obj = Class()
		current_obj_type = "Class"
		ast.append(current_obj) # TODO fix?
	else:
		expecting = expecting[1:] # rest of classdecs is empty
		add_to_ast(token) # find a new handler
		
def handle_classdec(token):
	global expecting
	global current_obj
	global current_obj_type
	if assert_obj_type("Class"):
		# expect id first
		if current_obj.id == None:
			if is_id(token):
				current_obj.set_id(token)
			else:
				throw_error("Encountered " + token + " while expecting a typeid for a <classdec>")
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
		elif token == "implements":
			if current_obj.expecting_more_vars:
				throw_error("Syntax error", addl="Expecting another typevar")
			else:
				expecting.insert(0, "<implements-rest>")
		elif '{' in token:
			if current_obj.expecting_more_vars:
				throw_error("Syntax error", addl="Expecting another typevar")
			elif len(current_obj.implements) < 1:
				throw_error("Class " + current_obj.id + " must implement <typeapps>")
			else:
				if '{' == token:
					expecting.insert(0, "<classbody>")
				else:
					throw_error("Syntax error while parsing a <classdec>")
		elif '}' in token:
			if '}' is token:
				expecting = expecting[1:] # consume token, done with classdec
			else:
				read_tight_code(token)
		else:
			throw_error("Encountered " + token + " while parsing a " + str(current_obj_type))
	else:
		throw_error("Syntax error while parsing a <classdec>")
	
def handle_extends(token):
	global expecting
	global current_obj
	global current_obj_type
	if expecting[0] == "<extends-rest>":
		if ',' in token:
			if ',' == token:
				throw_error("Syntax error while parsing <typeapps> of a <protodec>")
			else:
				read_tight_code(token)
		else:
			if is_typeapp(token):
				current_obj.add_extends(token)
				expecting[0] = "<extends>"
			else:
				throw_error("Encountered " + token + " while expecting a <typeapp> for Protocol " + current_obj.typeid)
	elif expecting[0] == "<extends>":
		# expecting ',' or end of implements here
		if ',' in token:
			if ',' == token:
				expecting[0] = "<extends-rest>"
			else:
				read_tight_code(token)
		else:
			expecting = expecting[1:]
			add_to_ast(token) # return to handler
	
def handle_implements(token):
	global expecting
	global current_obj
	global current_obj_type
	if expecting[0] == "<implements-rest>":
		if ',' in token:
			if ',' == token:
				throw_error("Syntax error while parsing <typeapps> of a <classdec>")
			else:
				read_tight_code(token)
		else:
			if is_typeapp(token):
				current_obj.add_implements(token)
				expecting[0] = "<implements>"
			else:
				throw_error("Encountered " + token + " while expecting a <typeapp> for Class " + current_obj.id)
	elif expecting[0] == "<implements>":
		# expecting ',' or end of implements here
		if ',' in token:
			if ',' == token:
				expecting[0] = "<implements-rest>"
			else:
				read_tight_code(token)
		else:
			expecting = expecting[1:]
			add_to_ast(token) # return to handler
			
			
def handle_classbody(token):
	global expecting
	global current_obj
	global current_obj_type
	# already took care of {
	# now expecting ( <formals> ) <block> <bodydecs> }
	if not assert_obj_type("Class"):
		throw_error("Encountered a <classbody> while not parsing a <classdec>")
	else:
		if '(' in token:
			if '(' is token:
				current_obj.found_formals()
				expecting.insert(0, "<formals>")
			else:
				read_tight_code(token)
		else:
			if current_obj.expecting_formals:
				throw_error("Expecting (<formals>) for <init> of <classbody>")
			elif '{' in token:
				if '{' is token:
					expecting.insert(0, "<block>")
					if current_obj:
						push_stack()
					current_obj = Block()
					current_obj_type = "Block"
				else:
					read_tight_code(token)
			# assume block handler adds the block to our obj and consumes }
			else:
				expecting.insert(0, "<bodydecs>")
				add_to_ast(token) # don't consume token
				# then bodydecs TODO   <constdec> or <globaldec> or <fielddec> or <fundec>
				# finally if }, return, consume expecting, don't consume token (classdec will)

		# TODO ensure added all this back to current obj
		# -- add_block
		# -- add_bodydec
		
# redirecter for figuring out which dec is next
def handle_bodydecs(token):
	global expecting
	global current_obj
	global current_obj_type
	# each dec will add itself to obj, return on }
	if "constant" == token:
		expecting.insert(0, "<constdec>")
		if current_obj:
			push_stack()
		current_obj = Constdec()
		current_obj_type = "Constdec"
	elif "static" == token:
		expecting.insert(0, "<globaldec>")
		if current_obj:
			push_stack()
		current_obj = Globaldec()
		current_obj_type = "Globaldec"
	elif "fun" == token:
		expecting.insert(0, "<fundec>")
		if current_obj:
			push_stack()
		current_obj = Fundec()
		current_obj_type = "Fundec"
	elif is_type(token):
		expecting.insert(0, "<fielddec>")
		if current_obj:
			push_stack()
		current_obj = Fielddec()
		current_obj_type = "Fielddec"
		add_to_ast(token) # don't consume token
	elif '}' in token:
		if '}' is token:
			expecting = expecting[1:]
	
	
def handle_funprotos(token):
	global expecting
	global current_obj
	global current_obj_type
	if token == "fun":
		expecting.insert(0, "<funproto>")
		if current_obj:
			push_stack()
		current_obj = Funproto()
		current_obj_type = "Funproto"
		ast.append(current_obj) # TODO fix?
	else:
		expecting = expecting[1:] # rest of funprotos is empty
		add_to_ast(token) # find a new handler
	
def handle_funproto(token):
	global expecting
	global current_obj
	global current_obj_type
	if not assert_obj_type("Funproto"):
		throw_error("Funproto expected")
	else:
		if current_obj.id == None:
			# expect id first
			if is_id(token):
				current_obj.set_id(token)
			else:
				throw_error("Encountered " + token + " while expecting an <id> for a <funproto>")
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
		elif '(' in token:
			if current_obj.expecting_more_vars:
				throw_error("Syntax error", addl="Expecting another typevar")
			else:
				if '(' == token:
					#expecting = expecting[1:] # rest of funprotos is formals, possibly rtype
					expecting.insert(0, "<formals>")
				else:
					read_tight_code(token)
		elif ':' in token:
			if ':' is token:
				expecting.insert(0, "<rtype>")
			else:
				read_tight_code(token)
		elif ';' is token:
			expecting = expecting[1:] # end of fun proto
			fp_obj = current_obj
			pop_stack()
			current_obj.add_funproto(fp_obj)
		else:
			throw_error("Syntax error in <funproto>", addl="Did you forget a semicolon or parenthesis?")
		
		
def handle_constdec(token):
	# assume constant token was already consumed
	global expecting
	global current_obj
	global current_obj_type
	if not assert_obj_type("Constdec"):
		throw_error("Constdec expected")
	else:
		if current_obj.type is None:
			if not token in PRIMTYPES:
				throw_error("Encounted " + token + " while expecting a <primtype> for <constdec>")
			else:
				current_obj.set_type(token)
		elif current_obj.id is None:
			if not is_id(token):
				throw_error(token + " is not a valid <id> for <constdec>")
			else:
				current_obj.set_id(token)
		elif not current_obj.eq:
			if token == ASSIGNOP:
				current_obj.consume_eq()
			else:
				throw_error("Expecting <assignop> while parsing <constdec>")
		elif current_obj.lit is None:
			if not is_literal(token):
				throw_error(token + " is not a valid <literal> for <constdec>")
			else:
				current_obj.lit = token
		elif ';' in token:
			if ';' is token:
				expecting = expecting[1:] # consume char, done
				dec_obj = current_obj
				pop_stack()
				current_obj.add_formal(dec_obj) # FIXME, should be add_dec
			else:
				read_tight_code(token)
				
def handle_globaldec(token):
	# assume static token was already consumed
	global expecting
	global current_obj
	global current_obj_type
	if not assert_obj_type("Globaldec"):
		throw_error("Globaldec expected")
	else:
		if current_obj.type is None:
			if not token in PRIMTYPES:
				throw_error("Encounted " + token + " while expecting a <primtype> for <globaldec>")
			else:
				current_obj.set_type(token)
		elif current_obj.id is None:
			if not is_id(token):
				throw_error(token + " is not a valid <id> for <globaldec>")
			else:
				current_obj.set_id(token)
		elif not current_obj.eq:
			if token == ASSIGNOP:
				current_obj.consume_eq()
			else:
				throw_error("Expecting <assignop> while parsing <globaldec>")
		elif current_obj.lit is None:
			if not is_literal(token):
				throw_error(token + " is not a valid <literal> for <globaldec>")
			else:
				current_obj.lit = token
		elif ';' in token:
			if ';' is token:
				expecting = expecting[1:] # consume char, done
				dec_obj = current_obj
				pop_stack()
				current_obj.add_formal(dec_obj) # FIXME, should be add_dec
			else:
				read_tight_code(token)
		

def handle_fielddec(token):
	global expecting
	global current_obj
	global current_obj_type
	if not assert_obj_type("Fielddec"):
		throw_error("Fielddec expected")
	else:
		if current_obj.type is None:
			if not is_type(token):
				throw_error("Encounted " + token + " while expecting a <type> for <fielddec>")
			else:
				current_obj.set_type(token)
		elif current_obj.id is None:
			if not is_id(token):
				throw_error(token + " is not a valid <id> for <fielddec>")
			else:
				current_obj.set_id(token)
		elif ';' in token:
			if ';' is token:
				expecting = expecting[1:] # consume char, done
				dec_obj = current_obj
				pop_stack()
				current_obj.add_formal(dec_obj) # FIXME, should be add_dec
			else:
				read_tight_code(token)
		

def handle_fundec(token):
	global expecting
	global current_obj
	global current_obj_type
	if not assert_obj_type("Fundec"):
		throw_error("Fundec expected")
	else:
		if current_obj.id == None:
			# expect id first
			if is_id(token):
				current_obj.set_id(token)
			else:
				throw_error("Encountered " + token + " while expecting an <id> for a <fundec>")
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
		elif '(' in token:
			if current_obj.expecting_more_vars:
				throw_error("Syntax error", addl="Expecting another typevar")
			else:
				if '(' == token:
					#expecting = expecting[1:] # rest of fundec is formals, possibly rtype
					expecting.insert(0, "<formals>")
				else:
					read_tight_code(token)
		elif ':' in token:
			if ':' is token:
				expecting.insert(0, "<rtype>")
			else:
				read_tight_code(token)
		elif '{' in token:
			if '{' is token:
				expecting.insert(0, "<block>")
				if current_obj:
					push_stack()
				current_obj = Block()
				current_obj_type = "Block"
			else:
				read_tight_code(token)
		elif '}' is token:
			expecting = expecting[1:] # end of fundec
			fd_obj = current_obj
			pop_stack()
			current_obj.add_dec(fd_obj) # FIXME?
		else:
			throw_error("Syntax error in <fundec>")
		
		
		
def handle_exp(token, end):
	throw_error("Parser not defined for syntax <exp>") # TODO
	if token == end:
		pass # TODO return constructed exp to prev object
	
def handle_exp_semi(token):
	handle_exp(token, ';')
	
def handle_exp_paren(token):
	handle_exp(token, ')')
	
def handle_exp_bracket(token):
	handle_exp(token, ']')

def handle_block(token):
	global expecting
	global current_obj
	global current_obj_type
	if not assert_obj_type("Block"):
		throw_error("Block expected")
	else:
		if current_obj.dec_phase:
			if "fun" is token:
				expecting.insert(0, "<fundec>")
				add_to_ast(token) # return to handler
			elif is_type(token):
				expecting.insert(0, "<vardec>")
				add_to_ast(token) # return to handler
			else:
				current_obj.end_decs()
				add_to_ast(token) # return to handler
		elif '}' in token: # stms expected until }
			if '}' is token:
				# add block to its parent object
				block_obj = current_obj
				pop_stack()
				current_obj.add_block(block_obj)
				expecting = expecting[1:] # block finished
			else:
				read_tight_code(token)
		else:
			expecting.insert(0, "<stm>")
			add_to_ast(token)
	
	
# redirect to more specific stm handlers based on first token of stm
def handle_stm(token):
	global expecting
	for key in STM_REDIRECTS.keys():
		if key in token:
			if key == token:
				expecting[0] = STM_REDIRECTS[key]
				if key != "return": # consume return
					add_to_ast(token) # return to handler
			else:
				read_tight_code(token)
	
def handle_stm_empty(token):
		throw_error("Parser not defined for syntax <stm-empty>") # TODO

def handle_stm_if(token):
	throw_error("Parser not defined for syntax <stm-if>") # TODO

def handle_stm_while(token):
	throw_error("Parser not defined for syntax <stm-while>") # TODO
	
def handle_stm_for(token):
	throw_error("Parser not defined for syntax <stm-for>") # TODO
	
def handle_stm_return(token):
	global expecting
	if ';' == token:
		expecting = expecting[1:] # consume ;
	else:
		expecting[0] = "<exp-semi>"
		add_to_ast(token)

def handle_stm_halt(token):
	throw_error("Parser not defined for syntax <stm-halt>") # TODO
	
def handle_factor(token):
	# check for factor-unop
	for u in UNOPS:
		if u in token:
			if u is token:
				expecting[0] = "<factor-unop>"
				add_to_ast(token) # return to handler
				return
			else:
				read_tight_code(token)
	if is_literal(token):
		expecting[0] = "<factor-lit>"
		add_to_ast(token) # return to handler
	elif token == "new":
		expecting[0] = "<factor-new>"
		add_to_ast(token) # return to handler
	elif token == "lambda":
		expecting[0] = "<factor-lam>"
		add_to_ast(token) # return to handler
	elif '(' in token:
		if '(' is token:
			expecting[0] = "<factor-exp>"
			# consume (
		else:
			read_tight_code(token)
	elif is_id(token):
		expecting[0] = "<factor-id>"
		add_to_ast(token)
	else:
		throw_error("Syntax error while parsing <factor>")
			
def handle_factor_unop(token):
	throw_error("Parser not defined for syntax <factor-unop>") # TODO
	
def handle_factor_lit(token):
	throw_error("Parser not defined for syntax <factor-lit>") # TODO
	
def handle_factor_lam(token):
	throw_error("Parser not defined for syntax <factor-lam>") # TODO
	
def handle_factor_exp(token):
	throw_error("Parser not defined for syntax <factor-exp>") # TODO
	
def handle_factor_id(token):
	throw_error("Parser not defined for syntax <factor-id>") # TODO
		
# push current object to stack
def push_stack():
	global current_obj
	global current_obj_type
	global object_stack
	global object_stack_type
	object_stack.insert(0, current_obj)
	object_type_stack.insert(0, current_obj_type)
	current_obj = None
	current_obj_type = None
	
# pop object from stack to current
def pop_stack():
	global current_obj
	global current_obj_type
	global object_stack
	global object_type_stack
	current_obj = object_stack[0]
	current_obj_type = object_type_stack[0]
	object_stack = object_stack[1:]
	object_type_stack = object_type_stack[1:]

def is_type(token): # TODO more needed here
	valid = False
	valid = valid or token in PRIMTYPES
	valid = valid or is_typeapp(token)
	# TODO array, can be <type> []
	# TODO can be function ( ( <types> ) ARROW <rtype> )
	return valid
	
def is_rtype(token):
	return token is "void" or is_type(token)
		

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
	valid = valid and not is_reserved(token)
	return valid
	
def is_reserved(token):
	return token in RESERVED
	
	
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
	
def is_typeapp(token): # TODO, can also be <typeid> < <types> >
	return is_id(token) or is_tvar(token)


TOKEN_TO_HANDLER = { 
"<protodecs>" : handle_protodecs,
"<protodec>" : handle_protodec,
"<classdecs>" : handle_classdecs,
"<classdec>" : handle_classdec,
"<funprotos>" : handle_funprotos,
"<funproto>" : handle_funproto,
"<formals>" : handle_formals,
"<formals-rest>" : handle_formals,
"<formal>" : handle_formal,
"<rtype>" : handle_rtype,
"<implements>" : handle_implements,
"<implements-rest>" : handle_implements,
"<classbody>" : handle_classbody,
"<bodydecs>" : handle_bodydecs,
"<constdec>" : handle_constdec,
"<globaldec>" : handle_globaldec,
"<fielddec>" : handle_fielddec,
"<fundec>" : handle_fundec,
"<exp-semi>" : handle_exp_semi,
"<exp-paren>" : handle_exp_paren,
"<exp-bracket>" : handle_exp_bracket,
"<stm>" : handle_stm,
"<stm-empty>" : handle_stm_empty,
"<stm-if>" : handle_stm_if,
"<stm-while>" : handle_stm_while,
"<stm-for>" : handle_stm_for,
"<stm-ret>" : handle_stm_return,
"<stm-halt>" : handle_stm_halt,
"<block>" : handle_block,
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