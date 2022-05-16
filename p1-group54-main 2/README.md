# Checkpoint 1 Work

Name: Ashwath Raghav Swaminathan And Shaunak Wagh

We implemented an implicit free list to simulate mm_init, malloc, free and realloc.

The algorithm that we used for finding memory blocks(malloc) to store values is the First-Fit Algorithm. This is a temporary solution for find fit as it reduces our memory utilisation value.

# Final Submission Work

For Checkpoint 2, we implemented an explicit free list(A separate list for storing addresses of free blocks) and a heap checker but then we observed that we had 0 throughput.
 
 Since, implementing an Explicit Free list resulted in a bad throughput(=0), even though utilisation was fairly good(50), we implemented segregated list concept where each segregated list holds blocks of one particular size. Thus, we can perform find fit, without a helper function separately and we can do the same in place function. The algorithm for find fit implicitly becomes Best Fit Algorithm. We moved to segregated lists to boost throughput but our utilisation went down! Maybe because of the tradeoff between utilisation and throughput.
