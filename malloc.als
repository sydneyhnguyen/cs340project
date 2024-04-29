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
  nex: lone Word,
}

sig NormalWord extends Word {
  inBlock: lone Block,  
}

one sig HeapHeader extends Word {
  first: lone Block
}

one sig HeapFooter extends Word {}

/*
sig HeaderWord extends Word{
  inBlock: lone Block,
  size: Int
}

sig FooterWord extends Word{
  inBlock: lone Block,
  size: Int
}*/

// prede: relation Block -> Block 
// succ: relation Block -> Block

// prede and succ are each a subset of Block x Block

sig Block {
  status: Status, 
  prede: lone Block, 
  succ: lone Block,
  words: set NormalWord
}

fact WordSuccession {
  // A more verbose way to write the following statement:
  //all a, b : Block | a->b in prede <=> b->a in succ

  // Relational operator: ~ is transpose (switch order)
  ~prede = succ
  ~pre = nex
  all disj x,y : NormalWord | y in x.^nex or y in x.^pre  // connected 
  no HeapHeader.pre
  all x: NormalWord | x in HeapHeader.^nex
  no HeapFooter.nex
  all x: NormalWord | x in HeapFooter.^pre
}

// Each word corresponds to only one block

pred OneBlockPerWord {
  all w:NormalWord, b:Block | w->b in inBlock <=> b->w in words
 // ~words = inBlock
}

pred mm_init {
  one Block
  Block.status = Free
  Block.words = NormalWord
  OneBlockPerWord
  HeapHeader.first = Block
  //#NormalWord > 4
}

/*
pred mm_malloc [x:int] {
  
}
*/
run mm_init for 8 but exactly 8 Word
run {
some b: Block | #b.words > 1
} for 3 but exactly 3 Block
// Only consecutive words can point to same block


// mm_init()

 
