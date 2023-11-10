module Utils.All where

data All b = ANil
           | ACons b (All b)

