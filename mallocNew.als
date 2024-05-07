abstract sig Status {} 
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

one sig HeapHeader extends Word {}
one sig HeapFooter extends Word {}


var sig Block {
  var status: Status, 
  var prede: lone Block, 
  var succ: lone Block,
  var words: set NormalWord
}

fact WordSuccession {
  ~prede = succ
  ~pre = nex
  all disj x,y : NormalWord | y in x.^nex or y in x.^pre  // connected 
  // HeapHeader is first
  no HeapHeader.pre
  all x: NormalWord | x in HeapHeader.^nex
  // HeapFooter is last
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
  Block.status = Free
  Block.words = NormalWord
  OneBlockPerWord
  no prede
  no succ
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
      Block' = Block + y + z - b
      words' = words - b->b.words + y->y.words' + z->z.words'
      #(y.words') = add[x,1]
      b.words = y.words' + z.words'
      inBlock' = ~words'
      status' = status + y->Alloc + z->Free - b->Free

      // Update block succession
      succ' = succ + y->z - b->b.succ + z->b.succ + b.prede->y - b.prede->b
      prede' = ~succ'
      
      //Fix the order of allocated words
      // There's no word in z that precedes a word in y
      all w1:y.words' | {
        all w2:z.words' | w2 not in w1.^pre
      }
    }
  }
}


/*
pred free [b:Block] {
  b.status = Alloc and {
    status' = status + b->Free - b->Alloc
    Block' = Block
    prede' = prede
    succ' = succ
    words' = words
    inBlock' = inBlock  
    
    no disj b1,b2:Block | b2 = b1.succ and b1.status = Free and b2.status = Free => after doNothing
    some disj b1,b2:Block |  b2 = b1.succ and b1.status = Free and b2.status = Free => {
      after coalesce
      after after coalesce
    } 
   
    //some disj b1,b2:Block |  b2 = b1.succ and b1.status = Free and b2.status = Free => {
     // after after coalesce
    //}
  }
} 

pred coalesce {
  some disj b1,b2:Block |  b2 = b1.succ and b1.status = Free and b2.status = Free and {
    one x:Block' | x not in Block and x in Block' and {
      status' = status - b1->Free - b2->Free + x->Alloc
      Block' = Block - b1 - b2 + x
      words' = words - b1->b1.words - b2->b2.words + x->b1.words + x->b2.words
      x.words' = b1.words + b2.words
      inBlock' = ~words'
      succ' = succ - b1->b2 - b2->b2.succ + x->b2.succ - b1.prede->b1 + b1.prede->x
      prede' = ~succ'
    }
  }  
  //no disj b1,b2:Block | b2 = b1.succ and b1.status = Free and b2.status = Free => doNothing
} */

pred free [b:Block] {
  b.status = Alloc => {
    status' = status + b->Free - b->Alloc
    Block' = Block
    prede' = prede
    succ' = succ
    words' = words
   
    some disj b1,b2:Block |  b2 = b1.succ and b1.status = Free and b2.status = Free => {
      after coalesce
    } 
    some disj b1,b2:Block |  b2 = b1.succ and b1.status = Free and b2.status = Free => {
      after after coalesce
    } 
   /*
  after coalesce
  after after coalesce
   */
  }
  b.status = Free => doNothing
  
}

pred coalesce {
  some disj b1,b2:Block |  b2 = b1.succ and b1.status = Free and b2.status = Free and {
    one x:Block' | x not in Block and x in Block' and {
      status' = status - b1->Free - b2->Free + x->Alloc
      Block' = Block - b1 - b2 + x
      words' = words - b1->b1.words - b2->b2.words + x->b1.words + x->b2.words
      x.words' = b1.words + b2.words
      succ' = succ - b1->b2 - b2->b2.succ + x->b2.succ - b1.prede->b1 + b1.prede->x
      prede' = ~succ'
    }
  }  
  //no disj b1,b2:Block | b2=b1.succ and b1.status = Free and b2.status = Free => doNothing
}
pred mm_malloc [x:Int] {
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

fact validTraces {
  mm_init
  always (
    some i:Int | i<#NormalWord and mm_malloc[i] or
    some b:Block | b.status = Alloc and free[b] or
    doNothing
  ) eventually (some b: Block | b.status = Alloc and free[b])
} 
//run validTraces for 10 but exactly 10 Word, 5 Int 


assert noAdjFreeBlocks {
  always (some b:Block | b.status = Alloc and free[b] => eventually(no disj b1,b2:Block | b1.succ = b2 and b1.status = Free and b2.status = Free))
}
 
check noAdjFreeBlocks for 8 but exactly 8 Word, 5 Int

// Run to check that coalesce works on the case where three blocks should merge
run {
  mm_init
  mm_malloc[1]
  after mm_malloc[1]
  after after mm_malloc[1]
  after after after {one b1:Block | no b1.prede and b1.status = Alloc and free[b1]}
  after after after after {one b2:Block | no b2.succ and b2.status = Alloc and free[b2]}
  after after after after after {one b3:Block | b3.status = Alloc and free[b3]}  
} for 8 but exactly 8 Word, 5 Int

run {
  mm_init
  mm_malloc[1]
  after (some b:Block | b.status = Alloc and free[b])
} for 8 but exactly 8 Word, 5 Int

/*
  after mm_malloc[1]

  after after mm_malloc[1]
  after after after {one b1:Block | no b1.prede and b1.status = Alloc and free[b1]}
  after after after after {one b2:Block | no b2.succ and b2.status = Alloc and free[b2]}
  after after after after after {one b3:Block | b3.status = Alloc and free[b3]}  */

