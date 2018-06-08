# LL(k) Parser Lookahead Optimization
---
Presented is a LL(k) lookahead process for a network protocol parser generator that generates parser source code from descriptions of protocols in the [SCL5](https://dl.acm.org/citation.cfm?id=1105634.1105646) notation. This LL(k) module performs *k* lookahead passed on the data structures to determine if the instance type of a union can be determined by unique value restrictions placed on fields of the union types.

### Why LL(k)
The previous LL(1) system also presented here, while useful was not able to cover all optimization cases due to its restriction to a single level of lookahead. There would be many instances where two types shared a value restriction, which would cause the LL(1) to fail. The by moving to *k* lookahead passes, it is possible to optimize for all cases. The lookahead system also remains efficient as *k* has an upper bound to the number of value restrictions, which in practice will always be a reasonable number.

### Technical Specification
---
The LL(k) lookahead system is written in the source transformation language [TXL](https://txl.ca). The system will deconstruct the initial source into its different fields and then perform analysis to search for optimization opportunities. It starts by examining areas where the original LL(1) optimization failed, as a time saving measure. As further lookahead finds additional optimization opportunities, it will construct an annotation to describe the value restriction pattern that can be later transformed into source code in an efficient one-to-one coupling, to parse that type. The grammar for the annotation and an example are presented below, as the main contributiuon of this research.

#### Annotation Grammar
![Grammar](https://i.imgur.com/9CaDYrX.png "Annotation Grammar")

##### Example
Consider the following example for a union consisting of the following types with restrictions:
| Type        | Restriction 1 | Restriction 2 | Restriction 3 |
| ----------- |:---------------:|:---------------:|:---------------:|
| ACK | MessageType = 1 | -- | -- |
| Data | MessageType = 2 | Payload = 1 | -- |
| DataHello | MessageType = 2 | Payload = 0 | CommunicationType = 24 |
| DataRequest | MessageType = 2 | Payload = 0 | CommunicationType = 90 |
A union consisting of these four types and their restrictions, where Restriction 1 and 2 are 1 byte and Restriction 3 is 2 bytes would produce the annotation:
```
< lookahead >
	@ MessageType
	    ACK @ 1
	END <MessageType @ 1> Data, DataHello, DataRequest @ 2
	@ Payload
	    Data @ 1
	END <Payload @ 1> DataHello, DataRequest @ 0
	@ CommunicationType
	    DataHello @ 24
	    DataRequest @ 90
	END
< /lookahead >
		
```

## Documentation
---
This work has a supporting technical IEEE paper describing the research in more detail, available [here](https://1drv.ms/b/s!AuxEJ0tR77ULxS-AJbzMwbXhwU45).

### Compilation
The work `generateLLKOptimizations.txl` is provided strictly as an example of how to implement the annotation process described in the work. It is a single module of the full parser generator system and requires the initial closed source generator modules to run properly. This module only is provided open source to further research in this area.

---
##### Citation
Thank you to Ali El-Shakankiry for authoring the original LL(1) optimization that was the basis for this work. His source `generateOptimizations.txl` is presented here as an additional reference to the lookahead process.

© Queen's University 2017