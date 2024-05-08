# cs340project


## How to install required tools (you can link to tool pages for the main instructions).
	
	Alloy download: https://alloytools.org/download.html 
	Sterling download: https://sterling-js.github.io/download/ 

## How to run the project.

	To run our project, you can execute our run statements and our check statement to view temporal instances of our model. The visualizations can be recreated using Sterling’s visualizer depending on how you would like to visualize the instances.To visualize temporal instances, you must go into the XML file created from a run statement and create individual XML files for each instance ensuring that the heading & footer of the original XML file is present in each instance XML, as well as edit “backloop” to 0 and “traces; to 1.

## The general problem our project is tackling

Our project addresses the topic of memory allocation in C, by modeling behavior of malloc and related functions. Memory allocation is critical to allow programmers to dynamically allocate and free memory when they are unaware of how much memory or how long they will need to allocate something prior to executing a program. To model the behavior of memory allocation, we ended up modeling the functions mm_init(), mm_malloc(), allocate(), mm_free(), coalesce(). In addition to modeling, we were also interested in verifying the correctness of these functions. To accomplish this, we wrote test run cases and an assertion to check that free blocks were properly coalesced.
After we decided on memory allocation as our project topic, we also added another component of creating custom visualizations of the behavior of the memory heap during execution of memory allocation functions. To achieve this, we used XML files that were exported from Alloy’s existing visualation tool, and we used Stering which is a web-based visualizer that takes XML files from Alloy and allows users to more easily change the exising visualization.

## Tradeoffs and attempted approaches

We first tried to represent the behavior of malloc by including block headers and block footers as extending Block, however, we realized that this approach was quite complicated, and we were able to model this behavior by having blocks keep track of their status, size, predecessor, and successor. There were many approaches made for the coalesce function, 

What assumptions did you make about scope? What are the limits of your model?
	
We made a number of assumptions about scope to simplify modeling the behavior of malloc. One of our major design choices was deciding to malloc in words which represent 8 bytes instead of trying to malloc bytes directly themselves. This ensured that we could focus on the higher level behavior of malloc instead of tryung to manipulate integer values in Alloy. In addition to this, we are assuming that any call to malloc is aligned to 8 bytes, and we are accounting for block headers by adding 1 word to the size of words that we are hoping to malloc. This additional word represents the block header. We also assume that all calls to malloc and free are legal, i.e. malloc is called only when there exists some block that can accommodate the allocation, and free is called only when there is some allocated block to free.

Additionally, another challege we faced on the visualization side was the obstacle of visualizing temporal instances in Sterling. Sterling does not currently support traces and backloops, so it was quite challenging to explore how to modify the XML files of a temporal instance to individual XMls for each trace of the instance. We were able to resolve this issue by representing each trace as an individual representation, however, this results in slight differences between each trace of the temporal instance. 
