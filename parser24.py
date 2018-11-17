#! /usr/bin/env python2.7
"""
CS 7400
Quirk 24 Parser
Author: Josh Miller
"""

SPACE = 0x20
LF = 0xa
CR = 0xd
COMMENT = "//" # followed by LF or CR
ASSIGNOP = "="
OROP = "||"
ANDOP = "&&"
RELOPS = ["==", "!=", "<", "<=", ">", ">="]
ADDOPS = ["+", "-"]
MULOPS = ["*", "/"]
UNOPS = ["!", "-"]
illegal = False

# TODO
#  - tab characters are illegal


def run(input, output):
	import os
	ast = []
	
	with open(input, 'r') as file:
		pass
		
		
	with open(output, 'w') as file:
		if illegal:
			file.write("(illegal)")
		else:
			file.write(ast_to_string(ast, "", 0))


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