# cs340project

How to install required tools (you can link to tool pages for the main instructions).

How to run your project.

The general problem your project is tackling.

Our project will address the topic of memory allocation in C, by modeling behavior of malloc and related functions. We also plan on creating visualizations of memory heap behavior during execution of memory allocation functions by parsing outputted Alloy XML files. The languages we will use are Alloy, for modeling, and Python, for visualizations. 
More specifically, we hope to model and visualize (in Python) the functions mm_init(), mm_malloc(), allocate(), mm_free(), coalesce(), and hopefully explicit free lists. In addition to modeling this behavior of memory allocation, we are also interested in verifying the correctness of these functions. To accomplish this, we will write predicate statements which we will hopefully be able to test with assert & check statements.

What tradeoffs did you make in choosing your representation? What else did you try that didn’t work as well?
We first tried to represent the behavior of malloc by including block headers and block footers as extending Block, however, we realized that this approach was quite complicated, and we were able to model this behavior by having blocks keep track of their status, size, predecessor, and successor. 

What assumptions did you make about scope? What are the limits of your model?
We made a number of assumptions about scope to simplify modeling the behavior of malloc. One of our major design choices was deciding to malloc in words which represent 8 bytes instead of trying to malloc bytes directly themselves. This ensured that we could focus on the higher level behavior of malloc instead of tryung to manipulate integer values in Alloy. In addition to this, we are assuming that any call to malloc is aligned to 8 bytes, and we are accounting for block headers by adding 1 word to the size of words that we are hoping to malloc. This additional word represents the block header.
