import os
import sys
import marshal
import itertools
import argparse
from operator import itemgetter
from functools import partial
from collections import Counter

try:
    import cPickle as pickle
except:
    import pickle

termchar = 17 # Assume the byte 17 does not appear in the input file


#Huff Tree Node Implementation
class node:
    def __init__(self, freq, symbol, left=None, right=None):
        self.freq = freq
        self.symbol = symbol
        self.left = left
        self.right = right
        self.huff = ''


def findCodes(node, code_dict = {}, val=''):
    #return dictionary for all symbols/huffman codes when passed root of tree
    newVal = val + str(node.huff)
    if(node.left):
        findCodes(node.left, code_dict, newVal)
    if(node.right):
        findCodes(node.right, code_dict, newVal)
    #For leaf nodes: add symbol/huffcode pair to dictionary
    if(node.left == None and node.right == None):
        code_dict[node.symbol] = newVal
    return code_dict


#Input: String of bits of length <= 8
#Output: int representing value of the bits in the byte_string
def byteVal(byte_string):
    bit_length = len(byte_string)
    if(bit_length < 8):
        byte_string = byte_string + (8-bit_length)*'0'
    val = 0
    for i in range(0, 8, 1):
        val += int(byte_string[7-i]) * 2**i
    return val


#Input: int representation of a byte from a bytearray()
#Output: a string of bits representing that byte
def byteGetBits(byte):
    byteval = int(byte)
    byte_string = ''
    cur_bit = 7
    while(cur_bit >= 0):
        if(byteval >= 2**cur_bit):
            byteval -= 2**cur_bit
            byte_string += '1'
        else:
            byte_string += '0'
        cur_bit -= 1
    return byte_string


# This takes a sequence of bytes over which you can iterate, msg,
# and returns a tuple (enc,\ ring) in which enc is the ASCII representation of the
# Huffman-encoded message (e.g. "1001011") and ring is the ``decoder ring'' needed
# to decompress that message.
def encode(msg):
    msg = msg + termchar.to_bytes(1, byteorder='big')

    byte_freqs = {}
    for byte in msg:
        if byte not in byte_freqs:
            byte_freqs[byte] = 0
        byte_freqs[byte] += 1

    tree = []
    for byte in byte_freqs:
        tree.append(node(byte_freqs[byte], byte))

    #until 1 root
    while len(tree) > 1:
        #sort tree nodes by each node's frequency
        tree = sorted(tree, key=lambda x: x.freq)

        #two least frequently-appearing bytes
        left = tree[0]
        right = tree[1]

        #left = 0, right = 1
        left.huff = 0
        right.huff = 1

        #put left and right under one parent node
        parent = node(left.freq+right.freq, left.symbol+right.symbol, left, right)

        #remove left/right nodes from tree - find my parent's children
        tree.remove(left)
        tree.remove(right)
        tree.append(parent)

    #get a dictionary for easy byte/code conversions for encoding
    byte_codes = findCodes(tree[0])

    coded_msg = ''
    for byte in msg:
        coded_msg += byte_codes[byte]

    #make a list of byte values from huffman-coded bits
    byte_vals = []
    for i in range(0, len(coded_msg), 8):
        byte = coded_msg[i:i+8]
        byteval = byteVal(byte)
        byte_vals.append(byteval)

    #make bytearray from the list of byte values of coded message
    byte_msg = bytearray(byte_vals)
    c_msg = bytes(byte_msg)

    return c_msg, tree[0]


# This takes a string, cmsg, which must contain only 0s and 1s, and your
# representation of the ``decoder ring'' ring, and returns a bytearray msg which
# is the decompressed message.
def decode(cmsg, decoderRing):
    coded_msg = ''
    #get a bitstring from the input
    for byte in cmsg:
        bit_string = byteGetBits(byte)
        coded_msg += bit_string

    decoded_msg = bytearray()
    cur_node: node
    cur_node = decoderRing #this is the root of the huffman tree

    #parse bitstring to decode
    for bit in coded_msg:
        if bit == '0':
            cur_node = cur_node.left
        else:
            cur_node = cur_node.right
        #if leaf node
        if(cur_node.left == None and cur_node.right == None):
            decoded_msg.append(cur_node.symbol)
            cur_node = decoderRing

    #remove everything after the last occurence of byte 17
    term_index = 0
    for i in range(len(decoded_msg)-1, -1, -1):
        if(decoded_msg[i] == 17):
            term_index = i
            break

    for i in range(len(decoded_msg)-1, term_index-1, -1):
        del decoded_msg[i]

    return decoded_msg


# This takes a sequence of bytes over which you can iterate, msg, and returns a tuple (compressed, ring)
# in which compressed is a bytearray (containing the Huffman-coded message in binary,
# and ring is again the ``decoder ring'' needed to decompress the message.
def compress(msg, useBWT):

    if useBWT:
        msg = bwt(msg)
        msg = mtf(msg)

    compressed, tree = encode(msg)

    return compressed, tree


# This takes a sequence of bytes over which you can iterate containing the Huffman-coded message, and the
# decoder ring needed to decompress it.  It returns the bytearray which is the decompressed message.
def decompress(msg, decoderRing, useBWT):

    decompressedMsg = decode(msg, decoderRing)

    # before return, must invert the move-to-front and BWT
    if useBWT:
        decompressedMsg = imtf(decompressedMsg)
        decompressedMsg = ibwt(decompressedMsg)

    return decompressedMsg


# memory efficient inverse Burrows-Wheeler Transform
def ibwt(msg):
    totals = {}
    ranks = []
    index = 0
    for c in msg:
        if c == 17:
            termchar_index = index
        if c not in totals:
            totals[c] = 0
        ranks.append(totals[c])
        totals[c] += 1
        index += 1

    first = {}
    totc = 0
    for c, count in sorted(totals.items()):
        first[c] = (totc, totc + count)
        totc += count

    #rowi is first character in t, last char in return value, must start at termchar index
    rowi = termchar_index
    t = bytearray()
    while(len(t) < len(msg)):
        c = msg[rowi]
        t.append(c)
        rowi = first[c][0] + ranks[rowi]

    #reverse t and remove termchar at end
    return t[len(t)-1:0:-1]


# Burrows-Wheeler Transform functions
def radix_sort(values, key, step=0):
    #key is a function which returns a strip of text using (value,step)
    sortedvals = []
    radix_stack = []
    radix_stack.append((values, key, step))

    while len(radix_stack) > 0:

        values, key, step = radix_stack.pop()

        if len(values) < 2:
            for value in values:
                sortedvals.append(value)
            continue

        bins = {} #bins contains ASCII val as key, and a list of occurrence indexes in the msg
        for value in values:
            bins.setdefault(key(value, step), []).append(value)
        #for each ASCII val,
        for k in sorted(bins.keys()):
            radix_stack.append((bins[k], key, step + 1))
    return sortedvals


# memory efficient Burrows-Wheeler Transform
# msg is a bytes object. msg[1] is an ASCII integer from 0-255 reprenting an individual byte
def bwt(msg):
    #return the next length of the text file using the current value + step
    def bw_key(text, value, step):
        return text[(value + step) % len(text)]

    #converts 17 to b'\x11' = 16+1 in hexadecimal - this byte won't appear so its the terminating character
    msg = msg + termchar.to_bytes(1, byteorder='big')

    bwtM = bytearray()

    #partial object houses the function bw_key and msg as value
    rs = radix_sort(range(len(msg)), partial(bw_key, msg))
    for i in rs:
        bwtM.append(msg[i - 1])
    #rs is sortedvals, a list of indexes of chars. place characters in msg based off of radix-sortedvals

    #put it in reverse
    return bwtM[::-1]


# Move-to-Front Encoding Stage
def mtf(msg):
    # Initialise the list of characters (i.e. the dictionary)
    dictionary = bytearray(range(256))

    # Transformation
    compressed_text = bytearray()
    rank = 0

    # read in each character
    for c in msg:
        rank = dictionary.index(c) # find the rank of the character in the dictionary
        compressed_text.append(rank) # update the encoded text

        # update the dictionary
        dictionary.pop(rank)
        dictionary.insert(0, c)

    return compressed_text # Return the encoded text as well as the dictionary

# Inverse Move-to-Front Decoding Stage
def imtf(compressed_msg):
    compressed_text = compressed_msg
    dictionary = bytearray(range(256))

    decompressed_img = bytearray()

    # read in each character of the encoded text
    for i in compressed_text:
        # read the rank of the character from dictionary
        decompressed_img.append(dictionary[i])

        # update dictionary
        e = dictionary.pop(i)
        dictionary.insert(0, e)

    return decompressed_img # Return original string



if __name__=='__main__':

    parser = argparse.ArgumentParser(description='The Multi-Stage Encoding Compression (M-SEC) algorithm compresses '
                                                 'binary and plain text files using the Burrows-Wheeler transform, '
                                                 'move-to-front coding, and Huffman coding.')
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('-c', action='store_true', help='Compresses a stream of bytes (e.g. file) into a bytes.')
    group.add_argument('-d', action='store_true', help='Decompresses a compressed file back into the original input')
    group.add_argument('-v', action='store_true', help='Encodes a stream of bytes (e.g. file) into a binary string'
                                                       ' using Huffman encoding.')
    group.add_argument('-w', action='store_true', help='Decodes a Huffman encoded binary string into bytes.')
    parser.add_argument('-i', '--input', help='Input file path', required=True)
    parser.add_argument('-o', '--output', help='Output file path', required=True)
    parser.add_argument('-b', '--binary', help='Use this option if the file is binary and therefore '
                                               'do not want to use the BWT.', action='store_true')

    args = parser.parse_args()

    compressing = args.c
    decompressing = args.d
    encoding = args.v
    decoding = args.w


    infile = args.input
    outfile = args.output
    useBWT = not args.binary

    assert os.path.exists(infile)

    if compressing or encoding:
        fp = open(infile, 'rb')
        sinput = fp.read()
        fp.close()
        if compressing:
            msg, tree = compress(sinput,useBWT)
            fcompressed = open(outfile, 'wb')
            marshal.dump((pickle.dumps(tree), msg), fcompressed)
            fcompressed.close()
        else:
            msg, tree = encode(sinput)
            print(msg)
            fcompressed = open(outfile, 'wb')
            marshal.dump((pickle.dumps(tree), msg), fcompressed)
            fcompressed.close()
    else:
        fp = open(infile, 'rb')
        pck, msg = marshal.load(fp)
        tree = pickle.loads(pck)
        fp.close()
        if decompressing:
            sinput = decompress(msg, tree, useBWT)
        else:
            sinput = decode(msg, tree)
            print(sinput)
        fp = open(outfile, 'wb')
        fp.write(sinput)
        fp.close()
