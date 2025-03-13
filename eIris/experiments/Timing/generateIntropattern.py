import random
import sys

basePatterns = ['_' , '?' , '$' , '*' , '**' , '/=' , '//' , '!%', 'a'*100, '%'+'a'*100]

def createBasePattern(depth):
    return random.choice(basePatterns)

def createAndPattern(depth):
    return f"[{createIntropattern(depth)} {createIntropattern(depth)}]"

def createOrPattern(depth):
    return f"[{createIntropattern(depth)} | {createIntropattern(depth)}]"

patternGenrators = [createAndPattern, createOrPattern]

def createIntropattern(depth):
    if depth == 1:
        return createBasePattern(depth)
    
    f = random.choice(patternGenrators)
    return f(depth - 1)    

if __name__ == "__main__":
    depth = int(sys.argv[1])
    pattern = " ".join([createIntropattern(depth) for i in range(depth)])
    print(pattern)
