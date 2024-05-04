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
  var pre: lone Word,
  var nex: lone Word,
}

sig NormalWord extends Word {
  var inBlock: lone Block,  
}

one sig HeapHeader extends Word {
  var first: lone Block
}

one sig HeapFooter extends Word {}

sig HeaderWord extends NormalWord {}

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

var sig Block {
  var status: Status, 
  var prede: lone Block, 
  var succ: lone Block,
  var words: set NormalWord
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
  no HeaderWord
  Block.status = Free
  Block.words = NormalWord
  OneBlockPerWord
  HeapHeader.first = Block
  no prede
  no succ
  //#NormalWord > 4
}

pred can_malloc[b:Block, size:Int] {
  b.status = Free
  #b.words >= add[size,1]
  //no b1:Block | #b1.words >= add[size,1] and b1 in b.^prede
}

pred allocate [b:Block, x:Int] {
    //let inList = HeapHeader.first
//    let newBlock =  Block |
//    {
//	Block' = b + newBlock
//    	b.status' = Alloc
//       newBlock.status' = Alloc
//     }
/*
 some disj z, y:Block | z not in Block and y not in Block => {
//	let inList = heapHeader.next^next
//	// if space to allocate is enough, allocate whole block
//	// else, split block to allocate only necessary block
      Block' = Block + z + y
      z.words' + y.words' = b.words
      #z.words' = add[x,1]
      z.status' = Alloc
      y.status' = Free
    }  */
  not (#(b.words) > add[x, 1]) => {
    b.status' = Alloc
  }
  #(b.words) > add[x, 1] => {
    b.status' = Alloc
    //#(b.words') = add[x,1]
    //no b.words'
    one disj y,z:Block' | y not in Block and y in Block' and z in Block' and z not in Block and {
      y.status' = Alloc
      //no b.words''
      Block'' = Block + y + z -b
      b.words = y.words' + z.words'
      #(y.words') = add[x,1]
      z.status'=Free
      z.words' = b.words - y.words'
      all w:NormalWord, c:Block | w->c in inBlock' <=> c->w in words'
    }
  }
}

pred split[b,y,z:Block, x:Int] {
  y.status' = Alloc
  z.status' = Free
  b.words = y.words' + z.words'
  

}

pred mm_malloc [x:Int] {
-- preconditions
  some b:Block | can_malloc[b, x] and {
   allocate[b,x]
  //b.status' = Alloc
   
   b.words' = b.words
   prede' = prede
   succ' = succ 
   first' = first
   inBlock' = inBlock
pre' = pre
nex' = nex
 }
}

run 
// some disj f1, f2: Block | {
{mm_init and mm_malloc[3]
        } for 8 but exactly 8 Word, 5 Int

run {

} for 4 Int
// Only consecutive words can point to same block


// mm_init()

 

