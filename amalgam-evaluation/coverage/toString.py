import sys

content = sys.stdin.read()

print('\n'.join(['+ "{}\\n"'.format(x) for x in content.split('\n')]))
