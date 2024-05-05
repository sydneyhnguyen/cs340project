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
  //var first: lone Block
}

var sig Block {
  var status: Status, 
  var prede: lone Block, 
  var succ: lone Block,
  var words: set NormalWord
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
   // Case 1: No splitting required 
  not (#(b.words) > add[x, 1]) => {
    b.status' = Alloc
  }

   //Case 2: Splitting required, new block created 
  #(b.words) > add[x, 1] => {
    //b.status' = Alloc
    //#(b.words') = add[x,1]
    //no b.words'
    one disj y,z:Block' | y not in Block and y in Block' and z in Block' and z not in Block and {
      y.status' = Alloc
      z.status'=Free
      no b.words'
      Block' = Block + y + z - b
      #(y.words') = add[x,1]
      b.words = y.words' + z.words'
      z.words' = b.words - y.words'
      inBlock' = ~words'

      // Update block succession
      succ' = succ + y->z - b->b.succ + z->b.succ
      prede' = prede + z->y - b->b.prede + y->b.prede
      
      //Fix the order of allocated words
      // There's no word in z that precedes a word in y
      all w1:y.words' | {
        all w2:z.words' | w2 not in w1.^pre
      }
    }
  }
}

pred coalesce {
  some disj b1,b2:Block | b2 = b1.succ and b1.status = Free and b2.status = Free => {
    one x:Block' | x not in Block and x in Block' and {
      status' = status - b1->Free - b2->Free + x->Free
      Block' = Block - b1 - b2 + x
      x.words' = b1.words + b2.words
    }
  }
}

pred free {
  one b1:Block | b1.status = Alloc and status' = status + b1->Free
  //Block' = Block
  //prede' = prede
  //succ' = succ
  //words' = words
}

pred mm_malloc [x:Int] {
-- preconditions
  some b:Block | can_malloc[b, x] and {
   allocate[b,x]
  //b.status' = Alloc
   pre' = pre
   nex' = nex
 }
}

run {mm_init and mm_malloc[3] and after free
        } for 8 but exactly 8 Word, 5 Int

run {

} for 4 Int
// Only consecutive words can point to same block


// mm_init()

 

