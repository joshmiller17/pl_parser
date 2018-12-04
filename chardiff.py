from __future__ import print_function

WHITESPACE = [0x20, 0xa, 0xd, "	", "  "]

def run(f1, f2):
	import os
	
	s1 = ""
	s2 = ""
	
	with open(f1, 'r') as f:
		line = f.readline()
		while (line):
			s1 += ("".join(line.strip()))
			line = f.readline()
	with open(f2, 'r') as f:
		line = f.readline()
		while (line):
			s2 += ("".join(line.strip()))
			line = f.readline()
			
	try:
		for i in range(len(s1)):
			while s1[i] in WHITESPACE or s1[i].isspace():
				s1 = s1[:i] + s1[i+1:]
			while s2[i] in WHITESPACE or s2[i].isspace():
				s2 = s2[:i] + s2[i+1:]
			if s1[i] == s2[i]:
				continue
			else:
				print("<" + s1[i:])
				print(">" + s2[i:])
				exit(0)
	except IndexError as e:
		print("Good!")
		
def main():
	import argparse
	prog_desc = "Char diff by Josh Miller"
	parser = argparse.ArgumentParser(description=prog_desc)
	parser.add_argument('file1', help="Input 1")
	parser.add_argument('file2', help="Input 2")
	args = parser.parse_args()
	run(args.file1, args.file2)
	

if '__main__' == __name__:
	main()