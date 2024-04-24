/*

All blocks are "alloc" or "free". 
Blocks have at most one "predecessor"
                             
       HEAP        
   +-----------+ 
b0 |alloc 0b11 +
   +-----------+ 
b1 |    ???    |  
   +-----------+ 
b2 |free  0b?0 +
   +-----------+ 

The question: given that we don't know the allocation status of  ???, 
is it possible for us to know if the following is true?
    "There is some free block whose predecessor is allocated"
*/


// Descriptions of objects: "sig"
// abstract: don't have any just Status, have the sub-sigs
abstract sig Status {} 

// extend works like in an object-oriented language. 
// Alloc is a subset of Status. Free is a subset of Status.
// "one" here means there will only be one atom of each.
one sig Alloc extends Status {}
one sig Free extends Status {}

// Sig for words

abstract sig Word {
  pre: lone Word,
  next: lone Word,
}

sig NormalWord extends Word {
  inBlock: lone Block,  
}

one sig HeapHeader extends Word {}

one sig HeapFooter extends Word {}

sig HeaderWord extends Word{
  inBlock: lone Block,
  size: Int
}

sig FooterWord extends Word{
  inBlock: lone Block,
  size: Int
}

// prede: relation Block -> Block 
// succ: relation Block -> Block

// prede and succ are each a subset of Block x Block

sig Block {
  status: Status, 
  prede: lone Block, 
  succ: lone Block,
  words: set Word
}

// Note" "pred" is a keyword in Alloy, so we'll use "prede"
// instead. 

// "fact"s in Alloy are constraints that are always true. 
pred succession {
  // A more verbose way to write the following statement:
  //all a, b : Block | a->b in prede <=> b->a in succ

  // Relational operator: ~ is transpose (switch order)
  ~prede = succ
  ~pre = next
}

run succession for 5

// Only consecutive words can point to same block


// mm_init()

 
