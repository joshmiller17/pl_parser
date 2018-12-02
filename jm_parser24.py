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
INDENTATION = "  "
ARROW = "->"
PRIMTYPES = ["bool", "char", "string", "int", "float"]
WHITESPACE = [ SPACE, LF, CR ]
COMMENT = "//" # followed by LF or CR
ASSIGNOPS = ["="]
OROPS = ["||"]
ANDOPS = ["&&"]
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
expecting = ["<protodecs>", "<classdecs>", "<stm>", "<end>"] #initial syntax expectations
protocols = []
classes = []
stms = []
ast_string = ""
line_count = 0
typeids = []
exp_grammar_stack = []
EXP_GRAMMAR = ['(',')','[',']']
current_obj = None
current_obj_type = None
object_stack = [None]
object_type_stack = ["None"]
DEBUG_LEVEL = 2.5  # amount of debug output, range [0,3] in steps of 0.5 because debugging is messy



# TODO tricky to handle "int []" without some kind of lookahead function -- can also be any number of []s

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
		return recursive_ast_to_string(self, "", 0)

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
		return recursive_ast_to_string(self, "", 0)
		

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
		
	def add_block(self, b):
		self.block = b

	def add_formal(self, f):
		self.formals.append(f)
		
	def set_expecting(self, b):
		self.expecting_more_vars = b
		
	def set_rtype(self, r):
		self.rtype = r
		
	def __str__(self):
		return recursive_ast_to_string(self, "", 0)
		
class Formal:
	
	def __init__(self):
		self.type = None
		self.id = None
		
	def set_type(self, t):
		self.type = t
		
	def set_id(self, i):
		self.id = i
		
	def __str__(self):
		return recursive_ast_to_string(self, "", 0)
		
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
		
	def add_dec(self, b):
		self.bodydecs.append(b)
		
	def __str__(self):
		return recursive_ast_to_string(self, "", 0)
		
class Block:
	
	def __init__(self):
		self.local_decs = []
		self.stms = []
		self.dec_phase = True
		
	def add_dec(self, l):
		self.local_decs.append(l)
		
	def end_decs(self):
		self.dec_phase = False
		
	def add_stm(self, s):
		self.stms.append(s)
		
	def __str__(self):
		return recursive_ast_to_string(self, "", 0)
		
class Stm:
	def __init__(self):
		self.style = None # {"empty", "exp", "if", "while", "return", "block", "halt", "for"}
		self.exps = []
		self.stms = []
		self.independent = False
		self.block = None
		self.vardec = None
		
	def set_style(self, s):
		self.style = s
		
	def add_block(self, b):
		self.block = b
		
	def add_dec(self, d):
		self.vardec = d
		
	def add_exp(self, e):
		self.exps.append(e)
		
	def add_stm(self, s):
		self.stms.append(s)
		
	def __str__(self):
		return recursive_ast_to_string(self, "", 0)
		
		
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
		
	def consume_eq(self):
		self.eq = True
		
	def set_lit(self, l):
		self.lit = l
		
	def __str__(self):
		return recursive_ast_to_string(self, "", 0)
		
class Constdec(Dec):

	def __init__(self):
		Dec.__init__(self)
		self.dectype = "const"
		
class Vardec(Dec):

	def __init__(self):
		Dec.__init__(self)
		self.dectype = "var"
		self.exp = None
		
	def add_exp(self, e):
		self.exp = e
		
	def __str__(self):
		return recursive_ast_to_string(self, "", 0)
		
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
		
	def __str__(self):
		return recursive_ast_to_string(self, "", 0)

# general approach for handling <exp> is as follows:
# collect all tokens as a raw array of strings until we know grammatically the <exp> is done
# then make several passes through the <exp> to determine <factor>, <term>, <simple>, <conjunct>, etc.
class Exp:

	# EXPRESSIONS
	#    factor, factor-rest, etc
	#    simple is (term (addop simple)*) -- any terms joined by addops
	#    term: a term is a (factor (mulop factor)*) -- any factors joined by mulops

	#    disjunct is (conjunct (andop disjunct)*) -- any conjuncts joined by andop
	#    conjunct is (simple (relop simple)*) -- any simples joined by relops
	#    lhs is (disjunct (orop lhs)*) -- any disjuncts joined by orops
	#    exp is lhs (assignop exp)*

	def __init__(self):
		self.raw = [] # tokens known to be in <exp>
		self.grammar_stack = [] # for counting matching () and []
		self.index = 0 # used as a pointer to where in the raw array we're processing
		self.current_factor = None
		
	def raw_append(self, r):
		self.raw.append(r)
		
	def has_op(self, ops):
		for m in ops:
			if m in self.raw:
				return True
		return False
		
	def new_factor(self):
		if self.current_factor == None:
			self.current_factor = Factor()
		
	# iterate through raw string turning tokens into factors
	def make_factors(self):
		self.index = 0
		while self.index < len(self.raw):
			self.make_factor()
			try:
				if "Factor" == self.raw[self.index].type:
					if DEBUG_LEVEL > 1.5:
						print("DEBUG: factor index = " + str(self.index))
						print("DEBUG: raw = " + str(self.raw))
					self.index += 1
			except Exception as e:
				if illegal:
					return
	
	# handler for how to compose factor based on first token
	def make_factor(self):
		if DEBUG_LEVEL > 1.5:
			print("DEBUG: factor index = " + str(self.index))
			print("DEBUG: raw = " + str(self.raw))
			if DEBUG_LEVEL > 2.5:
				if illegal:
					return
				else:
					print("DEBUG: ------- waiting for ready (press enter to continue)")
					raw_input()
		# check for factor-unop
		token = self.raw[self.index]
		if DEBUG_LEVEL > 2.5:
			print("DEBUG: parsing factor token " + str(token))
		for u in UNOPS:
			if u in token:
				if u is token:
					self.new_factor()
					self.handle_factor_unop()
				else: # tight unop
					new_tokens = read_tight_code(token,internal=True)
					for n in new_tokens:
						self.raw.insert(i, n)
					return
		# no unop, continue
		if token == "new":
			self.raw.pop(self.index) # remove new
			self.new_factor()
			self.handle_factor_new()
		elif token == "lambda":
			self.raw.pop(self.index) # remove lambda
			self.new_factor()
			self.handle_factor_lam()
		elif '(' in token:
			if '(' is token:
				self.raw.pop(self.index) # remove (
				self.new_factor()
				self.handle_factor_exp()
			else:
				new_tokens = read_tight_code(token,internal=True)
				for n in new_tokens:
					self.raw.insert(i, n)
				return
		elif is_literal(token):
			self.new_factor()
			self.handle_factor_lit()
		elif is_id(token):
			self.new_factor()
			self.handle_factor_id()
		else:
			throw_error("Syntax error while parsing <factor>")
	
	def handle_factor_unop(self):
		if not self.current_factor:
			throw_error("Assertion error: current <factor> is None while parsing <unop>")
		if self.raw[self.index] not in UNOPS:
			throw_error("Expected <unop> while parsing <factor>")
		self.current_factor.set_unop(self.raw.pop(self.index))
		temp_factor = self.current_factor
		new_factor()
		temp_factor.set_subfactor(self.current_factor)
		temp_factor.set_valid(True)
		self.raw.insert(self.index, temp_factor)
		
	def handle_factor_lit(self):
		if not self.current_factor:
			throw_error("Assertion error: current <factor> is None while parsing <literal>")
		if not is_literal(self.raw[self.index]):
			throw_error("Expected <literal> while parsing <factor>")
		else:
			self.current_factor.set_literal(self.raw.pop(self.index))
			self.handle_factor_rest()
			
	def handle_factor_new(self):
		if not self.current_factor:
			throw_error("Assertion error: current <factor> is None while parsing new")
		if self.current_factor.id is None:
			if is_id(self.raw[self.index]):
				self.current_factor.set_id(self.raw.pop(self.index))
				self.handle_factor_new()
			else:
				throw_error("Syntax error: expected <id> while parsing <factor>")
		elif '(' in self.raw[self.index]:
			if '(' == self.raw[self.index]:
				# TODO this doesn't handle recursive actuals
				self.raw.pop(self.index)
				new_exp_end = self.raw.index(')')
				if new_exp_end == -1:
					throw_error("Syntax error while parsing <actuals> of <factor>")
				else:
					self.raw.pop(new_exp_end)
					new_exp = self.raw[self.index : new_exp_end]
					actuals = self.handle_actuals(new_exp)
					if len(actuals):
						for a in actuals:
							self.current_factor.add_actual(a)
					self.handle_factor_rest()
		else:
			throw_error("Syntax error while parsing <factor>")
					
	def handle_actuals(self, new_exp):
		# exp, exp, exp, exp )
		actuals = []
		current_exp = None
		for token in new_exp:
			if ',' in token:
				if ',' is token:
					if current_exp is not None:
						current_exp.compile()
						actuals.append(current_exp)
					else:
						throw_error("Syntax error while parsing <actuals>")
				else:
					throw_error("Not enough whitespace while parsing <actuals> of <factor>")
			else:
				if current_exp is None:
					current_exp = Exp()
				current_exp.raw_append(token)
		if current_exp is not None:
			current_exp.compile()
			actuals.append(current_exp)
		return actuals
	
	def handle_bracket_exp(self):
		current_exp = None
		for token in new_exp:
			if ']' in token:
				if ']' is token:
					if current_exp:
						current_exp.compile()
						return current_exp
				else:
					throw_error("Not enough whitespace while parsing end of [ <exp> ] of <factor>")
			else:
				if current_exp is None:
					current_exp = Exp()
				current_exp.raw_append(token)
		throw_error("Reached end of [ <exp> ] without encountering closing bracket")
		
				
	def handle_factor_lam(self):
		if not self.current_factor:
			throw_error("Assertion error: current <factor> is None while parsing lambda")
		throw_error("Parser not defined for syntax <factor-lam>") # TODO
		
	def handle_factor_exp(self):
		if not self.current_factor:
			throw_error("Assertion error: current <factor> is None while parsing <exp>")
		throw_error("Parser not defined for syntax <factor-exp>") # TODO
		
	def handle_factor_id(self):
		if not self.current_factor:
			throw_error("Assertion error: current <factor> is None while parsing <id>")
		throw_error("Parser not defined for syntax <factor-id>") # TODO
		
	def handle_factor_rest(self):
		if not self.current_factor:
			throw_error("Assertion error: current <factor> is None while parsing <factor-rest>")
		
		specials = ['(', '.', '[']
				
		handled = False
		
		if len(self.raw):
			for s in specials:
				if s in self.raw[self.index]:
					if s != token:
						new_tokens = read_tight_code(token,internal=True)
						for n in new_tokens:
							self.raw.insert(i, n)
						self.handle_factor_rest()
						return
					else:
						if s == '(':
							handled = True
							throw_error("TODO expect ( <actuals> ) <factor-rest>")
							pass # TODO expect ( <actuals> ) <factor-rest>
						elif s == '.':
							handled = True
							throw_error("TODO expect <id> <factor-rest>")
							pass # TODO expect . <id> <factor-rest>
						elif s == '[':
							handled = True
							throw_error("TODO expect [ <exp> ] <factor-rest>")
							pass # TODO expect [ <exp> ] <factor-rest>
						else:
							throw_error("Syntax error while parsing <factor-rest>")
		
		if not handled:
			# factor done
			self.current_factor.set_valid(True)
			self.raw.insert(self.index, self.current_factor)
		
		
	# Given raw string of <exp>, construct the abstract representations that compose it
	def compile(self):
		#try:  # TODO uncomment
		self.make_factors() # convert all pieces into factors and ops
	
		while self.has_op(MULOPS): # TODO assert left and right are factors
			for i in range(len(self.raw)):
				if self.raw[i] in MULOPS:
					term = Term()
					term.set_op = self.raw[i]
					term.set_right = self.raw.pop(i+1)
					term.set_left = self.raw[i-1]
					self.raw[i-1] = term
				
		while self.has_op(ADDOPS):# TODO assert left is term and right is simple
		# TODO convert any remaining to simple
			for i in range(len(self.raw)):
				if self.raw[i] in ADDOPS:
					simple = Simple()
					simple.set_op = self.raw[i]
					simple.set_right = self.raw.pop(i+1)
					simple.set_left = self.raw[i-1]
					self.raw[i-1] = simple
					
		while self.has_op(RELOPS):# TODO assert left and right are simples
		# TODO convert any remaining to conjunct
			for i in range(len(self.raw)):
				if self.raw[i] in RELOPS:
					conjunct = Conjunct()
					conjunct.set_op = self.raw[i]
					conjunct.set_right = self.raw.pop(i+1)
					conjunct.set_left = self.raw[i-1]
					self.raw[i-1] = conjunct
					
		while self.has_op(ANDOPS):# TODO assert left is conjunct and right is disjunct
		# TODO convert any remaining to disjunct
			for i in range(len(self.raw)):
				if self.raw[i] in ANDOPS:
					disjunct = Disjunct()
					disjunct.set_op = self.raw[i]
					disjunct.set_right = self.raw.pop(i+1)
					disjunct.set_left = self.raw[i-1]
					self.raw[i-1] = disjunct
					
		while self.has_op(OROPS):# TODO assert left is disjunct and right is lhs
		# TODO convert any remaining to lhs
			for i in range(len(self.raw)):
				if self.raw[i] in OROPS:
					lhs = LHS()
					lhs.set_op = self.raw[i]
					lhs.set_right = self.raw.pop(i+1)
					lhs.set_left = self.raw[i-1]
					self.raw[i-1] = lhs
					
		while self.has_op(ASSIGNOPS):# TODO assert left is lhs and right is exp
		# TODO convert any remaining to exp
			for i in range(len(self.raw)):
				if self.raw[i] in ASSIGNOPS:
					exp = Exp()
					exp.set_op = self.raw[i]
					exp.set_right = self.raw.pop(i+1)
					exp.set_left = self.raw[i-1]
					self.raw[i-1] = exp
					
		# TODO assert there is only one exp
		if len(self.raw) > 1 or len(self.raw) < 1:
			throw_error("Parser error handling <exp>", addl="expected exactly 1 <exp>, got " + str(len(self.raw)) + ": " + str(self.raw))
						
		# except Exception as e:# TODO uncomment
			# throw_error("Syntax error while parsing <exp>")
			# if DEBUG_LEVEL > 0.5:
				# print("DEBUG: Exception: " + str(e))
				
	def __str__(self):
		return recursive_ast_to_string(self, "", 0)

class Factor(): # TODO

	def __init__(self):
		self.type = "Factor"
		self.id = None
		self.unop = None
		self.subfactor = None
		self.valid = False
		self.literal = None
		self.actuals = []
		
	def set_valid(self, v):
		self.valid = v
		
	def set_unop(self, u):
		self.unop = u
		
	def set_id(self, i):
		self.id = i
		
	def add_actual(self, a):
		self.actuals.append(a)
		
	def set_subfactor(self, s):
		self.subfactor = s
		
	def set_literal(self, l):
		self.literal = l
		
	def __str__(self):
		return recursive_ast_to_string(self, "", 0)
				
class ExpPiece:

	def __init__(self):
		self.left = None
		self.op = None
		self.right = None
		self.type = None
		
	def set_left(self, l):
		self.left = l
		
	def set_op(self, o):
		self.op = o 
		
	def set_right(self, r):
		self.right = r
		
	def __str__(self):
		return recursive_ast_to_string(self, "", 0)
		
class LHS(ExpPiece):

	def __init__(self):
		ExpPiece.__init__(self)
		self.type = "LHS"
		
class Disjunct(ExpPiece):

	def __init__(self):
		ExpPiece.__init__(self)
		self.type = "Disjunct"
		
class Conjunct(ExpPiece):

	def __init__(self):
		ExpPiece.__init__(self)
		self.type = "Conjunct"
		
class Simple(ExpPiece):

	def __init__(self):
		ExpPiece.__init__(self)
		self.type = "Simple"
		
class Term(ExpPiece):

	def __init__(self):
		ExpPiece.__init__(self)
		self.type = "Term"
		

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


	
	
def run(input, output):
	import os
	global line_count
	global illegal
	
	with open(input, 'r') as file:
		line = file.readline()
		while (line):
			line_count += 1
			line = tokenize_line(line)
			if DEBUG_LEVEL > 2.5 and not illegal:
				print("DEBUG: ------- waiting for ready (press enter to continue)")
				raw_input()
			line = file.readline()		
		
	with open(output, 'w') as file:
		if illegal:
			file.write("(illegal)")
		else:
			if ast_string == "":
				ast_to_string()
			file.write(ast_string)

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
		if len(object_stack) > 0:
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
		if DEBUG_LEVEL > 2:
			print("DEBUG: Expecting: " + str(expecting))
	
	check_current_obj()
	
	if expecting[0] == "<end>":
		throw_error("Encountered token <" + token + "> while expecting end of program")

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
def read_tight_code(token, internal=False):
	tight_tokens = ['(', ')', '{', '}', ',', ':', ';']
	new_line = token
	for t in tight_tokens:
		new_line = new_line.replace(t, " " + t + " ")
	if DEBUG_LEVEL > 1:
		print("DEBUG: \'" + token + "\' loosened to \'" + new_line + "\'")
	if not internal:
		tokenize_line(new_line, repeat=True)
	else:
		return(new_line.split())
		
	
def assert_obj_type(t):
	#global current_obj_type
	if t == current_obj_type:
		return True
	else:
		throw_error("Parser Error: Encountered a " + t + " while expecting object of type " + str(current_obj_type))
		return False
	
	
def setup_ast_to_string(protocols, classes, stms):
	out = ""
	out += "(program"
	indent = 1	
	for p in protocols:
		out = recursive_ast_to_string(p, out, indent)
	for c in classes:
		out = recursive_ast_to_string(c, out, indent)
	for s in stms:
		out = recursive_ast_to_string(s, out, indent)
	out += ")"
	return out
	
	
def recursive_ast_to_string(obj, out, indent_level):
	if DEBUG_LEVEL > 1:
		print("DEBUG: PRINTING AST FOR " + obj.__class__.__name__)
	
	out += "\n" + INDENTATION * indent_level + "("
	
	if obj.__class__.__name__ == "Protocol":
		out += "protoDec " + str(obj.typeid) + " ( "
		for tvar in obj.typevars:
			out += str(tvar) + " "
		out += ") ("
		for typeapp in obj.extends:
			out += str(typeapp) + " "
		out += ") ("
		for fp in obj.funprotos:
			out = recursive_ast_to_string(fp, out, indent_level + 1)
		
	elif obj.__class__.__name__ == "Class":
		out += "classDec " + str(obj.id) + " ( "
		for tvar in obj.typevars:
			out += str(tvar) + " "
		out += ") ("
		for typeapp in obj.implements:
			out += str(typeapp) + " "
		out += ") (init ("
		for formal in obj.init_formals:
			out = recursive_ast_to_string(formal, out, indent_level + 1)
		out += ")"
		out = recursive_ast_to_string(obj.block, out, indent_level + 1)
		out += ") ("
		for bd in obj.bodydecs:
			out = recursive_ast_to_string(bd, out, indent_level + 1)
		out += ")"
		
	elif obj.__class__.__name__ == "Funproto":
		out += "funProto " + str(obj.id) + " ( "
		for tvar in obj.typevars:
			out += str(tvar) + " "
		out += ") ("
		for formal in obj.formals:
			out = recursive_ast_to_string(formal, out, indent_level + 1)
		out += ")"
		if obj.rtype:
			out += " " + str(obj.rtype) + " "
		else:
			out += "(void) "
		
	elif obj.__class__.__name__ == "Fundec":
		out += "funDec " + str(obj.id) + " ( "
		for tvar in obj.typevars:
			out += str(tvar) + " "
		out += ") ("
		for formal in obj.formals:
			out = recursive_ast_to_string(formal, out, indent_level + 1)
		out += ")"
		if obj.rtype:
			out += " " + str(obj.rtype) + " "
		else:
			out += "(void) "
		out = recursive_ast_to_string(obj.block, out, indent_level + 1)
		
	elif obj.__class__.__name__ == "Formal":
		out += "formal " + str(obj.type) + " " + str(obj.id) + ")"
		
	elif obj.__class__.__name__ == "Block":
		out += "block ( "
		for dec in obj.local_decs:
			out = recursive_ast_to_string(dec, out, indent_level + 1)
		out += ") ("
		for stm in obj.stms:
			out = recursive_ast_to_string(stm, out, indent_level + 1)
		out += ")"
		
	elif obj.__class__.__name__ == "Stm":
		if obj.style == "empty":
			out += "(skip)"
		elif obj.style == "exp":
			if len(obj.exps) != 1:
				# TODO delete
				for exp in obj.exps:
					print("EXP: " + str(exp))
				throw_error("Parser error: expected <expStm> to have exactly 1 <exp>, has " + str(len(obj.exps)))
			out += "(expStm "
			out = recursive_ast_to_string(obj.exps[0], out, indent_level + 1)
		elif obj.style == "if":
			if len(obj.exps) != 1 or len(obj.stms) != 2:
				throw_error("Parser error: expected <ifStm> to have exactly 1 <exp> and 2 <stm>")
			out += "("
			out = recursive_ast_to_string(obj.exps[0], out, indent_level + 1)
			out += " "
			out = recursive_ast_to_string(obj.stms[0], out, indent_level + 1)
			out += " "
			out = recursive_ast_to_string(obj.stms[1], out, indent_level + 1)
		elif obj.style == "while":
			if len(obj.exps) != 1 or len(obj.stms) != 1:
				throw_error("Parser error: expected <whileStm> to have exactly 1 <exp> and 1 <stm>")
			out += "while "
			out = recursive_ast_to_string(obj.exps[0], out, indent_level + 1)
			out = recursive_ast_to_string(obj.stms[0], out, indent_level + 1)
		elif obj.style == "for":
			if len(obj.exps) != 2 or len(obj.stms) != 1:
				throw_error("Parser error: expected <forStm> to have exactly 2 <exp> and 1 <stm>")
			out = recursive_ast_to_string(obj.vardec, out, indent_level + 1)
			new_stm = obj
			new_stm.set_style("while")
			increment_exp = new_stm.exps.pop(1)
			increment_stm = Stm()
			increment_stm.set_style("exp")
			increment_stm.add_exp(increment_exp)
			new_stm.add_stm(increment_stm)
			obj = recursive_ast_to_string(new_stm, out, indent_level + 1)
		elif obj.style == "return":
			if len(obj.exps):
				out += "(return "
				out = recursive_ast_to_string(obj.exps[0], out, indent_level + 1)
			else:
				out += "(return0)"
		elif obj.style == "block":
			out += "("
			out = recursive_ast_to_string(obj.block, out, indent_level + 1)
		elif obj.style == "halt":
			if len(obj.exps) != 1:
				throw_error("Parser error: expected <haltStm> to have exactly 1 <exp>")
			out += "(halt "
			out = recursive_ast_to_string(obj.exps[0], out, indent_level + 1)
		
	elif obj.__class__.__name__ == "Constdec":
		out += "constant " + str(obj.type) + " " + str(obj.id) + " " + str(obj.lit)
		
	elif obj.__class__.__name__ == "Vardec":
		out += "varDec " + str(obj.type) + " " + str(obj.id) + " "
		out = recursive_ast_to_string(obj.exp, out, indent_level + 1)
		
	elif obj.__class__.__name__ == "Globaldec":
		out += "static " + str(obj.type) + " " + str(obj.id) + " " + str(obj.lit)
		
	elif obj.__class__.__name__ == "Fielddec":
		out += "fieldDec (formal " + str(obj.type) + " " + str(obj.id)
		
	elif obj.__class__.__name__ == "Exp":
		for r in obj.raw:
			out = recursive_ast_to_string(r, out, indent_level + 1)
		pass # TODO
		
	elif obj.__class__.__name__ == "Factor":
		out += "TODO FACTOR " + str(obj.id) + " " + str(obj.unop) + " " + str(obj.subfactor) + " " + str(obj.literal) + " " + str(obj.actuals)
	
	elif obj.__class__.__name__ == "LHS":
		out += "TODO LHS " + str(obj.op) + " " + str(obj.left) + " " + str(obj.right)
	
	elif obj.__class__.__name__ == "Disjunct":
		out += "TODO DISJUNCT " + str(obj.op) + " " + str(obj.left) + " " + str(obj.right)
	
	elif obj.__class__.__name__ == "Conjunct":
		out += "TODO CONJUNCT " + str(obj.op) + " " + str(obj.left) + " " + str(obj.right)
	
	elif obj.__class__.__name__ == "Simple":
		out += "TODO SIMPLE " + str(obj.op) + " " + str(obj.left) + " " + str(obj.right)
	
	elif obj.__class__.__name__ == "Term":
		out += "TODO TERM " + str(obj.op) + " " + str(obj.left) + " " + str(obj.right)
		
	else:
		throw_error("Parser error while writing " + obj.__class__.__name__)

	out += ")"
	if DEBUG_LEVEL > 1:
		print(out)
	return out
	
def ast_to_string():
	return setup_ast_to_string(protocols, classes, stms)

		
def handle_protodecs(token):
	global expecting
	global current_obj
	global current_obj_type
	global protocols
	if token == "protocol":
		expecting.insert(0, "<protodec>")
		if current_obj:
			push_stack()
		current_obj = Protocol()
		current_obj_type = "Protocol"
		protocols.append(current_obj)
	else:
		# no more protodecs, find a new handler
		expecting = expecting[1:]
		add_to_ast(token)
		
		
def handle_protodec(token):
	global expecting
	global current_obj
	global current_obj_type
	if assert_obj_type("Protocol"):
		# expect id first
		if current_obj.typeid == None:
			if is_id(token):
				current_obj.set_typeid(token)
				add_typeid(token) # define new typeid
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
				if assert_obj_type("Protocol"):
					pop_stack()
				else:
					throw_error("Parser error handling <protodec>")
			else:
				read_tight_code(token)
		else:
			throw_error("Encountered " + token + " while parsing a " + str(current_obj_type))
	else:
		throw_error("Protocol expected")

		
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


def handle_classdecs(token):
	global expecting
	global current_obj
	global current_obj_type
	global classes
	if token == "class":
		expecting.insert(0, "<classdec>")
		if current_obj:
			push_stack()
		current_obj = Class()
		current_obj_type = "Class"
		classes.append(current_obj)
	elif '}' == token:
		expecting = expecting[1:] # rest of classdecs is empty
		pop_stack()
		
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
				throw_error("Encountered " + token + " while expecting an <id> for a <classdec>")
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
				if assert_obj_type("Class"):
					pop_stack()
				else:
					throw_error("Parser error handling <classdec>")
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
					expecting[0] = "<bodydecs-plus-bracket>"
					expecting.insert(0, "<block>")
					if current_obj:
						push_stack()
					current_obj = Block()
					current_obj_type = "Block"
				else:
					read_tight_code(token)
			# assume block handler adds the block to our obj
			else:
				throw_error("Syntax error while parsing <classbody>")
		
def handle_bodydecs_plus_bracket(token):
	if token != '}':
		throw_error("End of <block> expected before <bodydecs>")
	else:
		expecting[0] = "<bodydecs>"
		
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
			#print("Expecting: " + str(expecting)) # TODO remove
			expecting = expecting[2:] # done with class too
			#print("Expecting: " + str(expecting)) # TODO remove
			add_to_ast(token)
	
	
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
		
	
def handle_vardec(token):
	global expecting
	global current_obj
	global current_obj_type
	if not assert_obj_type("Vardec"):
		throw_error("Vardec expected")
	else:
		if current_obj.type is None:
			if not is_type(token):
				throw_error("Encounted " + token + " while expecting a <type> for <vardec>")
			else:
				current_obj.set_type(token)
		elif current_obj.id is None:
			if not is_id(token):
				throw_error(token + " is not a valid <id> for <vardec>")
			else:
				current_obj.set_id(token)
		elif not current_obj.eq:
				if token == ASSIGNOPS[0]:
					current_obj.consume_eq()
				else:
					throw_error("Expecting <assignop> while parsing <vardec>")
		elif current_obj.exp is None:
				expecting.insert(0, "<exp-semi>")
				add_to_ast(token)
		else:
			assert_obj_type("Vardec")
			expecting = expecting[1:] # consume char, done
			dec_obj = current_obj
			pop_stack()
			current_obj.add_dec(dec_obj)
			add_to_ast(token) # return to handler
	
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
			if token == ASSIGNOPS[0]:
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
				current_obj.add_dec(dec_obj)
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
			if token == ASSIGNOPS[0]:
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
				current_obj.add_dec(dec_obj)
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
				current_obj.add_dec(dec_obj)
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
			current_obj.add_dec(fd_obj)
		else:
			throw_error("Syntax error in <fundec>")
		
		
		
def handle_exp(token, end):
	global expecting
	global exp_grammar_stack
	global current_obj
	global current_obj_type
	
	if current_obj_type != "Exp":
		if current_obj:
			push_stack()
		current_obj = Exp()
		current_obj_type = "Exp"
	
	if len(token) > 1:
		for c in ['(',')', '[', ']']:
			if c in token:
				read_tight_code(token)
				return
		if ';' in token:
			if ';' == token:
				if ';' == end:
					current_obj.compile()
					# add exp to its parent object
					exp_obj = current_obj
					pop_stack()
					current_obj.add_exp(exp_obj)
					expecting = expecting[1:] # exp finished
			else:
				read_tight_code(token)
				return
		else:
			current_obj.raw_append(token) # if we got here, no special chars, just add token
	else:
		# single character
		if token == '(':
			exp_grammar_stack.insert(0, token)
			current_obj.raw_append(token) # single char is part of exp
		elif token == '[':
			exp_grammar_stack.insert(0, token)
			current_obj.raw_append(token) # single char is part of exp
		elif token == ')':
			if len(exp_grammar_stack) == 0:
				if token == end:
					current_obj.compile()
					# add exp to its parent object
					exp_obj = current_obj
					pop_stack()
					current_obj.add_exp(exp_obj)
					expecting = expecting[1:] # exp finished
				else:
					throw_error("Syntax error while parsing <exp>", addl="Mismatching parentheses")
			else:
				if '(' != exp_grammar_stack.pop(0):
					throw_error("Syntax error while parsing <exp>", addl="Mismatching parentheses")
				else:
					current_obj.raw_append(token) # single char is part of exp
		elif token == ']':
			if len(exp_grammar_stack) == 0:
				if token == end:
					current_obj.compile()
					# add exp to its parent object
					exp_obj = current_obj
					pop_stack()
					current_obj.add_exp(exp_obj)
					expecting = expecting[1:] # exp finished
				else:
					throw_error("Syntax error while parsing <exp>", addl="Mismatching brackets")
			else:
				if '[' != exp_grammar_stack.pop(0):
					throw_error("Syntax error while parsing <exp>", addl="Mismatching brackets")
				else:
					current_obj.raw_append(token) # single char is part of exp	
		elif token == ';':
			if len(exp_grammar_stack) == 0:
				current_obj.compile()
				# add exp to its parent object
				exp_obj = current_obj
				pop_stack()
				current_obj.add_exp(exp_obj)
				expecting = expecting[1:] # exp finished
			else:
				throw_error("Syntax error while parsing <exp>", addl="Mismatching parentheses or brackets")
		else:
			current_obj.raw_append(token) # single char is part of exp
	
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
	if current_obj_type != "Block":
		if current_obj:
			push_stack()
		current_obj = Block()
		current_obj_type = "Block"
	else:
		if current_obj.dec_phase:
			if "fun" is token:
				expecting.insert(0, "<fundec>")
				if current_obj:
					push_stack()
				current_obj = Fundec()
				current_obj_type = "Fundec"
			elif is_type(token):
				expecting.insert(0, "<vardec>")
				if current_obj:
					push_stack()
				current_obj = Vardec()
				current_obj_type = "Vardec"
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
				add_to_ast(token) # don't consume token
			else:
				read_tight_code(token)
		else:
			expecting.insert(0, "<stm>")
			if current_obj:
				push_stack()
			current_obj = Stm()
			current_obj_type = "Stm"
			add_to_ast(token)
	
	
# redirect to more specific stm handlers based on first token of stm
def handle_stm(token):
	global expecting
	global current_obj
	global current_obj_type
	global stms
	if current_obj is None: # assume last stm of program
		current_obj = Stm()
		current_obj_type = "Stm"
		current_obj.independent = True
		stms.append(current_obj)
	assert_obj_type("Stm")
	handled = False
	for key in STM_REDIRECTS.keys():
		if key in token:
			handled = True
			if key == token:
				expecting[0] = STM_REDIRECTS[key]
				if key == "{" and current_obj.independent:
					expecting.insert(1, "<stm-finish>")
				if key != "return": # consume return
					add_to_ast(token) # return to handler
			else:
				read_tight_code(token)
	if not handled:
		expecting[0] = "<stm-exp>"
		add_to_ast(token)
		
def handle_stm_finish(token):
	global expecting
	if token == '}':
		expecting = expecting[1:]
	else:
		throw_error("Expected end of block")
	
def handle_stm_empty(token):
	global expecting
	global current_obj
	global current_obj_type
	current_obj.style = "empty"
	# add stm to its parent object
	if not current_obj.independent:
		stm_obj = current_obj
		pop_stack()
		current_obj.add_stm(stm_obj)

def handle_stm_if(token):
	global expecting
	global current_obj
	global current_obj_type
	throw_error("Parser not defined for syntax <stm-if>") # TODO

def handle_stm_while(token):
	global expecting
	global current_obj
	global current_obj_type
	throw_error("Parser not defined for syntax <stm-while>") # TODO
	
def handle_stm_for(token):
	global expecting
	global current_obj
	global current_obj_type
	throw_error("Parser not defined for syntax <stm-for>") # TODO
	
def handle_stm_exp(token):
	global expecting
	global current_obj
	global current_obj_type
	if expecting[0] == "<stm-exp>":
		current_obj.set_style("exp")
		expecting[0] = "<stm-exp-rest>"
		expecting.insert(0, "<exp-semi>")
		add_to_ast(token)
	elif expecting[0] == "<stm-exp-rest>":
		expecting = expecting[1:]
		# add stm to its parent object
		if not current_obj.independent:
			stm_obj = current_obj
			pop_stack()
			current_obj.add_stm(stm_obj)
			add_to_ast(token)
	
	else:
		throw_error("Syntax error while parsing <stm> :: <exp> ;")
	
def handle_stm_return(token):
	global expecting
	global current_obj
	global current_obj_type
	if ';' == token:
		current_obj.set_style("empty")
		expecting = expecting[1:] # consume ;
	else:
		expecting[0] = "<exp-semi>"
		add_to_ast(token)
	
	# add stm to its parent object
	if not current_obj.independent:
		stm_obj = current_obj
		pop_stack()
		current_obj.add_stm(stm_obj)

def handle_stm_halt(token):
	throw_error("Parser not defined for syntax <stm-halt>") # TODO
		
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
	if len(object_stack) > 0:
		current_obj = object_stack[0]
		current_obj_type = object_type_stack[0]
		object_stack = object_stack[1:]
		object_type_stack = object_type_stack[1:]
	else:
		current_obj = None
		current_obj_type = None

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
	valid = is_valid_char(token[0], mustbe=["digit"])
	if len(token) > 1:
		for c in token[1:]:
			valid = valid and is_valid_char(c, mustbe=["digit"])
	return valid
	
def is_floatliteral(token):
	if token.find('.') == -1 or len(token) < 2: # can't be just '.'
		return False
	else:
		before_dot = token[:token.find('.')]
		after_dot = token[(token.find('.')+1):]
	before_valid = len(before_dot) == 0 or is_intliteral(before_dot)
	if after_dot.find('e') == -1:
		after_valid = len(after_dot) == 0 or is_intliteral(after_dot)
	else:
		before_e = after_dot[:token.find('e')]
		after_e = after_dot[token.find('e'):]
		before_e_valid = len(before_e) == 0 or is_intliteral(before_e)
		e_valid = (after_e[0] == "+" and len(after_e) > 1) \
			or (after_e[0] == "-" and len(after_e) > 1) or is_intliteral(after_e[0])
		if len(after_e) > 1:
			e_valid = e_valid and after_e[1:]
		after_valid = before_e_valid and e_valid
	return before_valid and after_valid
	
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
	
def add_typeid(token):
	global typeids
	typeids.append(token)
	
def is_typeid(token):
	return token in typeids
	
def is_typeapp(token): # TODO, can also be <typeid> < <types> >
	return is_typeid(token) or is_tvar(token)


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
"<bodydecs-plus-bracket>" : handle_bodydecs_plus_bracket,
"<constdec>" : handle_constdec,
"<globaldec>" : handle_globaldec,
"<fielddec>" : handle_fielddec,
"<fundec>" : handle_fundec,
"<vardec>" : handle_vardec,
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
"<stm-exp>" : handle_stm_exp,
"<stm-exp-rest>" : handle_stm_exp,
"<stm-finish>" : handle_stm_finish,
"<block>" : handle_block,
}			
			
def main():
	import argparse
	global DEBUG_LEVEL
	prog_desc = "Quirk 24 parser by Josh Miller"
	parser = argparse.ArgumentParser(description=prog_desc)
	parser.add_argument('input', help="Input file name")
	parser.add_argument('output', help="Output file name")
	parser.add_argument('-debug', default=0, help="Level of debug info, from 0-3")
	args = parser.parse_args()
	DEBUG_LEVEL = float(args.debug)
	run(args.input, args.output)
	

if '__main__' == __name__:
	main()