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
  //all w:NormalWord, b:Block | w->b in inBlock <=> b->w in words
  ~words = inBlock
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
  no b1:Block | #b1.words >= add[size,1] and b1 in b.^prede and b1.status=Free
}

pred allocate [b:Block, x:Int] {
   // Case 1: No splitting required 
  not (#(b.words) > add[x, 1]) => {
    status' = status + b->Alloc - b->Free
    prede' = prede
    succ' = succ
    inBlock' = ~words'
    words' = words
    Block' = Block
  }

   //Case 2: Splitting required, new block created 
  #(b.words) > add[x, 1] => {
    one disj y,z:Block' | y not in Block and y in Block' and z in Block' and z not in Block and {
      //y.status' = Alloc
      //z.status'=Free
      Block' = Block + y + z - b
      words' = words - b->b.words + y->y.words' + z->z.words'
      #(y.words') = add[x,1]
      b.words = y.words' + z.words'
      inBlock' = ~words'
      status' = status + y->Alloc + z->Free - b->Free

      // Update block succession
      //y.succ' = z
      //y.prede' = b.prede
      //z.prede' = y
      //succ' = ~prede'
      //some b.prede => prede' = 
      //some b.succ => z.succ' = b.succ
      //z.succ' = b.succ
      succ' = succ + y->z - b->b.succ + z->b.succ + b.prede->y - b.prede->b
      prede' = ~succ'
      //prede' = prede + z->y - b->b.prede + y->b.prede
      
      //Fix the order of allocated words
      // There's no word in z that precedes a word in y
      all w1:y.words' | {
        all w2:z.words' | w2 not in w1.^pre
      }
    }
  }
}

pred free {
  one b1:Block | b1.status = Alloc and {
    status' = status + b1->Free - b1->Alloc
    Block' = Block
    prede' = prede
    succ' = succ
    words' = words
    inBlock' = inBlock
  }
}

pred coalesce {
  some disj b1,b2:Block | b2 = b1.succ and b1.status = Free and b2.status = Free => {
    one x:Block' | x not in Block and x in Block' and {
      //status' = status - b1->Free - b2->Free + x->Free
      Block' = Block - b1 - b2 + x
      //x.words' = b1.words + b2.words
      //inBlock' = ~words'
      //prede' = prede - b1->b1.prede - b2->b1 + x->b1.prede
      //succ' = succ - b1->b2 - b2->b2.succ + x->b2.succ - b1.prede->b1 + b1.prede->x
      //prede' = ~succ'
    }
  }
  no disj b1,b2:Block | (b2 = b1.succ and b1.status = Free and b2.status = Free) => doNothing
}

pred mm_malloc [x:Int] {
-- preconditions
  some b:Block | can_malloc[b, x] and {
   allocate[b,x]
  }
}

pred doNothing {
  Block' = Block
  status' = status
  prede' = prede
  succ' = succ
  words' = words
  inBlock' = inBlock
}

run {
  mm_init
  mm_malloc[1]
  after mm_malloc[1]
  after after free
  after after after coalesce
  //after after mm_malloc[1]
  //after after free
  //after after after coalesce
  //after after after free
  //after after after after coalesce
  //after after after after free
  //after after after coalesce
  //after after after free
  //after after doNothing
  //after mm_malloc[1]
  //after after mm_malloc[1]
  //after after after mm_malloc[1]
  //after after doNothing
  //after after mm_malloc[1]
} for 8 but exactly 8 Word, 5 Int

 

