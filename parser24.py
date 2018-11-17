#! /usr/bin/env python2.7
"""
CS 7400
Quirk 24 Parser
Author: Josh Miller
"""

def run(input, output):
	import os
	
	with open(input, 'r') as file:
		pass
		
		
	with open(output, 'w') as file:
		pass


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