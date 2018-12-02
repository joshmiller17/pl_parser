from __future__ import print_function

def run(input, output, all):
	import os
	
	out_file = open(output, 'w')
	with open(input, 'r') as in_file:
		
		line = in_file.readline()
		while (line):
			if all:
				print("".join(line.strip()), file=out_file, end='\n')
			else:
				print(line.lstrip(), file=out_file, end='')
			line = in_file.readline()

	out_file.close()
		
def main():
	import argparse
	prog_desc = "Whitespace stripper by Josh Miller"
	parser = argparse.ArgumentParser(description=prog_desc)
	parser.add_argument('input', help="Input file name")
	parser.add_argument('output', help="Output file name")
	parser.add_argument('--all', action='store_true', help="Remove all whitespace")
	args = parser.parse_args()
	run(args.input, args.output, args.all)
	

if '__main__' == __name__:
	main()