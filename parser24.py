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

# TODO
#  handlers for:
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
#    literal
#    charliteral
#    floatliteral -- ignore for now, handle later
#    exponent  -- ignore for now, handle later


def throw_error(line, reason)
	illegal = True
	error_line = line_count
	error_msg = reason + " encountered in line " + str(error_line)

def run(input, output):
	import os
	ast = []
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
	
def is_id(token):
	valid = is_valid_char(token[0], mustbe=["lower"])
	if len(token > 1):
		for c in token[1:]:
			valid = valid and is_valid_char(c, cantbe["print"]) # subsequent
	return valid
	
def is_tvar(token):
	valid = is_valid_char(token[0], mustbe=["upper"])
	if len(token > 1):
		for c in token[1:]:
			valid = valid and is_valid_char(c, cantbe["print"]) # subsequent
	return valid
	
def is_intliteral(token):
	valid = is_valid_char(token[0], mustbe["digit"]
	if len(token > 1):
		for c in token[1:]:
			valid = valid and is_valid_char(c, mustbe["digit"])
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
	
			
def tokenize_line(line):
	for c in line:
		current_token = ""
		if c in WHITESPACE:
			pass # TODO finish token
		elif is_valid_char(c):
			current_token += c # TODO anything else?
		else: #TODO handle
			throw_error(line_count, "Forbidden character: " + str(c))
			break
			
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