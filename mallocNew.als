abstract sig Status {} 
one sig Alloc extends Status {}
one sig Free extends Status {}

// Sig for words
abstract sig Word {
  pre: lone Word,
  nex: lone Word,
}

// Allocatable/free-able word
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

// Setup for underlying linked list of words
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
  ~words = inBlock
}

// Initializes heap with no allocated blocks
pred mm_init {
  one Block
  Block.status = Free
  Block.words = NormalWord
  OneBlockPerWord
  no prede
  no succ
}

// Malloc pred - takes size of block to be allocated
pred mm_malloc [x:Int] {
  some b:Block | can_malloc[b, x] and {
   allocate[b,x]
  }
}

// Helper pred to find blocks that can be allocated
pred can_malloc[b:Block, size:Int] {
  b.status = Free
  #b.words >= add[size,1]
  // Implements first-fit policy - this eligible block must be the first in the list
  no b1:Block | #b1.words >= add[size,1] and b1 in b.^prede and b1.status=Free
}

// Allocates blocks and adds one word to the requested number of words, symbolizing block headers
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

pred free [b:Block] {
  // Assumes that the given block is already Alloc
    // Case where no coalescing happens
    (b.prede.status = Alloc or no b.prede) and (b.succ.status = Alloc or no b.succ) => {
      status' = status - b->Alloc + b->Free
      Block' = Block
      words' = words
      inBlock' = inBlock
      prede' = prede
      succ' = succ
    }
    // Coalesce with successor, keeping b and removing the successor
    (b.prede.status = Alloc or no b.prede) and b.succ.status = Free => {
      status' = status - b.succ->Free + b->Free - b->Alloc
      Block' = Block - b.succ
      words' = words - b.succ->b.succ.words + b->b.succ.words
      inBlock' = ~words'
      succ' = succ - b.succ->b.succ.succ - b->b.succ + b->b.succ.succ
      prede' = ~succ'
  }
    // Coalesce with predecessor, keeping predecessor and removing b
    b.prede.status = Free and (b.succ.status = Alloc or no b.succ) => {
      status' = status - b->Alloc
      Block' = Block - b
      words' = words - b->b.words + b.prede->b.words
      inBlock' = ~words'
      succ' = succ - b.prede->b - b->b.succ + b.prede->b.succ
      prede' = ~succ'
    }
    //Coalesce with predecessor and successor, keeping only b
    b.prede.status = Free and b.succ.status = Free => {
      status' = status - b.prede->Free - b.succ->Free + b->Free - b->Alloc
      Block' = Block - b.prede - b.succ
      words' = words - b.prede->b.prede.words - b.succ->b.succ.words + b->b.prede.words + b->b.succ.words
      inBlock' = ~words'
      succ' = succ - b.prede.prede->b.prede - b.prede->b - b->b.succ - b.succ->b.succ.succ + b.prede.prede->b + b->b.succ.succ
      prede' = ~succ'
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

// Check that after free, no adjacent free blocks remain (coalesce works properly)
assert noAdjFreeBlocks {
  always (some b:Block | b.status = Alloc and free[b] => eventually(no disj b1,b2:Block | b1.succ = b2 and b1.status = Free and b2.status = Free))
}
 
check noAdjFreeBlocks for 8 but exactly 8 Word, 5 Int


// Checking validTraces
run {} for 8 but exactly 8 Word, 5 Int

// Testing each case of free/coalesce

// No coalesce happens
run noCoalescing {
  mm_init
  mm_malloc[1]
  after mm_malloc[1]
  after after mm_malloc[1]
  after after after (one b1:Block | one b1.prede and one b1.succ and free[b1])
  after after after after doNothing
} for 8 but exactly 8 Word, 5 Int

// Coalesce with successor
run coalesceWithSucc {
  mm_init
  mm_malloc[1]
  after (one b1:Block | b1.status = Alloc and free[b1])
} for 8 but exactly 8 Word, 5 Int

// Coalesce with predecessor
run coalesceWithPrede {
  mm_init
  mm_malloc[1]
  after mm_malloc[1]
  after after (one b1:Block | b1.prede.status = Alloc and b1.succ.status = Free and free[b1])
  after after after doNothing
} for 8 but exactly 8 Word, 5 Int

// Coalesce with both prede and succ
run coalesceThreeBlocks {
  mm_init
  mm_malloc[1]
  after mm_malloc[1]
  after after (one b1:Block | no b1.prede and b1.status = Alloc and free[b1])
  after after after (one b2:Block | one b2.prede and one b2.succ and free[b2])
} for 8 but exactly 8 Word, 5 Int

//=========ORIGINAL (not working) VERSIONS OF FREE AND COALESCE===========//
// Original free which used coalesce pred

/*
pred free [b:Block] {
  b.status = Alloc and {
    status' = status + b->Free - b->Alloc
    Block' = Block
    prede' = prede
    succ' = succ
    words' = words
    inBlock' = ~words'
    //after (some disj b1,b2:Block | b1->b2 in succ and b1.status = Free and b2.status = Free => coalesce [b1,b2])
    //some disj b1,b2:Block' |  b1->b2 in succ' and b1.status' = Free and b2.status' = Free => {
      //after coalesce
    //} 
    //some disj b1,b2:Block'' |  b1->b2 in succ'' and b1.status'' = Free and b2.status'' = Free => {
      //eafter after coalesce
    //} 
   
  after coalesce
  after after coalesce 
  }
  //b.status = Free => after doNothing
} */

// Coalesce adjacent free blocks into one free block - doesn't work but left in to show the process
pred coalesce{
  some disj b1,b2:Block |  b1->b2 in succ and b1.status = Free and b2.status = Free => {
    one x:Block' | x not in Block and x in Block' and {
      status' = status - b1->Free - b2->Free + x->Free
      Block' = Block - b1 - b2 + x
      words' = words - b1->b1.words - b2->b2.words + x->b1.words + x->b2.words
      x.words' = b1.words + b2.words
      x.prede' = b1.prede
      succ' = succ - b1.prede->b1 - b1->b2 - b2->b2.succ + b1.prede->x + x->b2.succ
      inBlock' = ~words'
    }
  }  
  no disj b1,b2:Block | b1->b2 in succ and b1.status = Free and b2.status = Free => doNothing
}
