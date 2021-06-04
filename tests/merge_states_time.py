# coding: utf-8

# In[1]:


import spot
from buddy import bddtrue as btrue
import time

# In[2]:

if __name__ == "__main__":
    autname = "aut.hoa"
    for opt in [True, False]:
        print(autname, opt)
        a = spot.automaton(autname)
        print(a.num_states())
        T = time.time()
        a.merge_states(opt)
        T = time.time() - T
        print(a.num_states)
        print("Total time ", T)