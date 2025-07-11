package main

import (
	"bufio"
	"fmt"
	"log"
	"os"
	"strconv"
	"strings"

	"github.com/developertruthstare/logger"
)

// Ran k-1 times at start of algorithm, takes time O(n) assuming creating a variable with number of bits = k is O(1). We will define this function as f(k). time F given k is assumed to be O(1). So the entire function is O(n * f(k)).
// O(n * f2(k)) where f2(x) is the time complexity of creating a variable with x bits
func CreateNodeList(n int, val ColorFlag) []ColorFlag {
	s := make([]ColorFlag, n)
	for i := range s {
		s[i] = val
	}
	return s
}

func main() {
	g, r := GetGraphFromFile("")
	err := g.Collapse()

	if err == nil { // three-colorable
		switch r {
		case UNKNOWN:
			logger.Success("System: three-colorable graph found by algorithm, but labeled as UNKNOWN. Checking new solution...")
		case TRUE:
			logger.Success("System: three-colorable graph found by algorithm.")
		case FALSE:
			logger.Warn("System: three-colorable graph found by algorithm, but labeled as not three-colorable. Checking new solution...")
		}

		logger.Info("Ensuring generated graph is valid...")
		err = CheckGraph(g)
		if err == nil {
			logger.Success("System Check: Generated graph is valid.")
			if r == FALSE {
				logger.Warn("Please update testing data to ensure accuracy.")
			}
			logger.Success("Result: Success")
		} else {
			logger.Error("System Check: Generated graph is not valid, %v\nResult: Failure", err)
		}
	} else {
		switch r {
		case UNKNOWN:
			logger.Success("System: Unlabeled graph, found to not be three-colorable by the algorithm.")
		case TRUE:
			logger.Warn("System: Labeled as three-colorable, but algorithm found it to be not three-colorable. Consider updating testing data.")
		case FALSE:
			logger.Success("System: Labeled as not three-colorable, and algorithm correctly determined so.")

		}
	}

	logger.Debug("Algorithm\t Labeled Data\n%t\t\t%t", err == nil, r == TRUE)
}

func (g *Graph) Collapse() error {
	// k * n space for k colors, n nodes
	listOfNodesInAnyPosition := CreateList(len(g.Nodes), func(i int) int {
		return int(i)
	}) // exactly k bits are set for k colors
	listOfNodesInSuperPosition := []int{} // exactly two bits are set
	listOfNodesCollapsed := []int{}       // exactly one bit is set
	listOfPropagatedNodes := []int{}

	loops := 0
	defer func() {
		logger.Info("Number of loops: %d", loops)
	}()

	// Worst case scenario: O(k * n) - because when this is executed, there is a 100% chance that at least one node will move from layer x to x-1. This means that in the worst case, we will have to move n ndoes down one layer k times
	for len(listOfPropagatedNodes) < len(g.Nodes)-1 {
		loops++
		// for generalized k colors, this would be a for loop over k times
		if len(listOfNodesCollapsed) > 0 {
			// Propagate the collapsed node's color to its neighbors
			collapsedNode := listOfNodesCollapsed[len(listOfNodesCollapsed)-1]
			listOfNodesCollapsed = listOfNodesCollapsed[:len(listOfNodesCollapsed)-1]

			// This is technically worst case O(n*n(-1)/2) but on average O(sqrt(n)) because we perform no operations in the case that a connection does not contain the chosen node. and there can be at most n*(n-1)/2 edges in the graph
			// So including the previous loop, the sum of the total times this loop will not perform no operations is O(k * n * n * (n-1)/2) = O(k * n^3) - polynomial time
			for _, edge := range g.Edges { // on average sqrt(n) times
				if edge.First != collapsedNode && edge.Second != collapsedNode {
					continue
				}
				neighbor := edge.First
				if edge.First == collapsedNode {
					neighbor = edge.Second
				}

				g.Nodes[neighbor] = g.Nodes[neighbor] & ^g.Nodes[collapsedNode]

				if g.Nodes[neighbor] == ERROR {
					logger.Success("Conclusion: Graph is not three-colorable")
					return fmt.Errorf("Graph cannot be three-colored due to conflict at node %d", neighbor)
				}
				if Contains(listOfPropagatedNodes, neighbor) {
					continue // already propagated this node
				}
				// Remove g.Nodes[neighbor] from the list that it's currently in
				listOfNodesInAnyPosition = RemoveInstance(listOfNodesInAnyPosition, neighbor)
				listOfNodesInSuperPosition = RemoveInstance(listOfNodesInSuperPosition, neighbor)

				switch g.Nodes[neighbor] {
				case RED, GREEN, BLUE:
					listOfNodesCollapsed = append(listOfNodesCollapsed, neighbor)
				case ANTI_RED, ANTI_GREEN, ANTI_BLUE:
					listOfNodesInSuperPosition = append(listOfNodesInSuperPosition, neighbor)
				default:
					logger.Error("Node %d is %b after being propagated from node %d of color %b\n", neighbor, g.Nodes[neighbor], collapsedNode, g.Nodes[collapsedNode])
				}
			}
			listOfPropagatedNodes = append(listOfPropagatedNodes, collapsedNode)
		} else if len(listOfNodesInSuperPosition) > 0 {
			node := -1
			// This can be done in O(n) time with a connection matrix created prior to the algorithm being ran, which can be done in O(n) time where n is the number of edges in the total graph
			for _, searchNode := range listOfNodesInAnyPosition {
				if node != -1 {
					continue
				}
				for _, connection := range g.Edges {
					if node != -1 {
						continue
					}
					if connection.First != searchNode && connection.Second != searchNode || node != -1 {
						continue
					}
					neighborA := connection.First
					if neighborA == searchNode {
						neighborA = connection.Second
					}
					for _, connectionB := range g.Edges {
						if connectionB.First != searchNode && connectionB.Second != searchNode {
							continue
						}
						neighborB := connectionB.First
						if neighborB == searchNode {
							neighborB = connection.Second
						}
						if neighborB == neighborA {
							continue
						}

						for _, connectionC := range g.Edges {
							if (connectionC.First == neighborA && connectionC.Second == neighborB) || (connectionC.First == neighborB && connectionC.Second == neighborA) {
								if g.Nodes[neighborA] == g.Nodes[neighborB] {
									node = searchNode
									g.Nodes[node] = ^g.Nodes[neighborB]
									RemoveInstance(listOfNodesInAnyPosition, node)
									listOfNodesCollapsed = append(listOfNodesCollapsed, node)
									continue
								}
							}
						}
					}
				}
			}
			if node != -1 {
				continue
			}

			node = listOfNodesInSuperPosition[len(listOfNodesInSuperPosition)-1]
			listOfNodesInSuperPosition = listOfNodesInSuperPosition[:len(listOfNodesInSuperPosition)-1]

			switch g.Nodes[node] {
			case ANTI_RED:
				g.Nodes[node] = GREEN
			case ANTI_GREEN:
				g.Nodes[node] = BLUE
			case ANTI_BLUE:
				g.Nodes[node] = RED
			}
			listOfNodesCollapsed = append(listOfNodesCollapsed, node)
		} else if len(listOfNodesInAnyPosition) > 0 {
			node := listOfNodesInAnyPosition[len(listOfNodesInAnyPosition)-1]
			listOfNodesInAnyPosition = listOfNodesInAnyPosition[:len(listOfNodesInAnyPosition)-1]
			// Assign a color to the node
			g.Nodes[node] = RED // or GREEN, or BLUE based on some strategy
			listOfNodesCollapsed = append(listOfNodesCollapsed, node)
		} else {
			// No more nodes to process, we are done
			logger.Error("This should not happen, but we are done processing nodes.")
			break
		}
	}
	return nil
}

func Contains[T comparable](lst []T, val T) bool {
	for _, v := range lst {
		if v == val {
			return true
		}
	}
	return false
}

// Assume there is only one instance of the value in the list
func RemoveInstance[T comparable](l []T, value T) []T {
	for i, v := range l {
		if v == value {
			return append(l[:i], l[i+1:]...)
		}
	}
	return l // return the original list if value not found
}

// the []int here is actually returning a complete list of indecies of nodes in the graph
// O(n * f1(n)) where f1(x) is the time complexity of creating a variable with log base 2 of x bits
func CreateList[T any](n int, lambda func(int) T) []T {
	s := make([]T, n)
	for i := range s {
		s[i] = lambda(i)
	}
	return s
}

// Only used as the value for the isSolveable label provided in the testing data
type BoolQ uint

const (
	TRUE    BoolQ = 1 << iota    // 0b001
	FALSE                        // 0b010
	UNKNOWN BoolQ = TRUE | FALSE // 0b011
)

// k bit value, color k is represented by 2^(k-1) in binary
type ColorFlag uint

// The definitions of all these colors is probably not necessary, but if they are they take up 2^k variables of k bits, requiring a total of 2^(k+1) bits
const (
	ERROR      ColorFlag = 0                  // 0b000
	RED        ColorFlag = 1 << iota          // 0b001
	GREEN                                     // 0b010
	BLUE                                      // 0b100
	ANY        ColorFlag = RED | GREEN | BLUE // 0b111 = 0x7
	ANTI_RED   ColorFlag = (^RED & ANY)       // 0b110
	ANTI_GREEN ColorFlag = (^GREEN & ANY)     // 0b101
	ANTI_BLUE  ColorFlag = (^BLUE & ANY)      // 0b011
)

// A list of n ColorFlags representing the coloring of a n node graph. Total size is n * 2^k bits for k colors and n nodes
// Edges is a list of pairs of unsigned integers representing the edges of the graph. Maximum size is log(n) * n * n(-1)/2 bits.		-   				the same effect can be achieved using n * (n-1)/2 bits in a 2d graph representation
type Graph struct {
	Nodes []ColorFlag      // 2^k bits for k colors
	Edges []Pair[int, int] // len(edges) <= n*(n-1)/2
}

func NewGraph(n int, edges []Pair[int, int]) *Graph {
	nodes := make([]ColorFlag, 0, n)
	for i := range n {
		nodes[i] = ANY
	}

	return &Graph{
		Nodes: []ColorFlag{},
		Edges: edges,
	}
}

// defined as a pair[any, any], but only used as pair[int, int], but realistically could be pair[uint, uint]
// but MORE ACCURATELY, it should be pair[T, T] where T is a customly implemented data type taking up minimal space = len(edges) <= n * (n-1)/2 and can be translated to a big number
type Pair[T1, T2 any] struct {
	First  T1
	Second T2
}

// Helper functions to create a graph, not part of algorithm
func GetGraphFromFile(filename string) (*Graph, BoolQ) {
	file, err := os.Open(filename)
	if err != nil {
		log.Fatalf("failed to open file: %v", err)
	}
	defer file.Close()

	var n int
	var edges []Pair[int, int]
	var label BoolQ = UNKNOWN

	scanner := bufio.NewScanner(file)
	for scanner.Scan() {
		line := scanner.Text()
		if strings.HasPrefix(line, "p") {
			parts := strings.Fields(line)
			if len(parts) >= 4 {
				n, _ = strconv.Atoi(parts[2])
			}
		} else if strings.HasPrefix(line, "e") {
			parts := strings.Fields(line)
			if len(parts) == 3 {
				u, _ := strconv.Atoi(parts[1])
				v, _ := strconv.Atoi(parts[2])
				edges = append(edges, Pair[int, int]{u, v})
			}
		} else if strings.HasPrefix(line, "v") {
			parts := strings.Fields(line)
			if len(parts) == 2 {
				val, _ := strconv.ParseBool(parts[1])
				tmp := new(bool)
				*tmp = val
				if tmp != nil && *tmp {
					label = TRUE
				} else if tmp != nil && !*tmp {
					label = FALSE
				}
			}
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatalf("error reading file: %v", err)
	}

	var lowestNumber int = 9999999999

	for _, edge := range edges {
		if edge.First < lowestNumber {
			lowestNumber = edge.First
		}
		if edge.Second < lowestNumber {
			lowestNumber = edge.Second
		}
	}
	if lowestNumber != 0 {
		logger.Warn("Graph is %d indexed, adjusting to 0-based indexing...", lowestNumber)
	}
	for i := range len(edges) {
		if edges[i].First-lowestNumber > n-1 {
			logger.Error("Edge (%d, %d) exceeds the number of vertices %d", edges[i].First, edges[i].Second, n-1)
			os.Exit(1)
		} else if edges[i].Second-lowestNumber > n-1 {
			logger.Error("Edge (%d, %d) exceeds the number of vertices %d", edges[i].First, edges[i].Second, n-1)
			os.Exit(1)
		}
		edges[i].First = edges[i].First - lowestNumber
		edges[i].Second = edges[i].Second - lowestNumber
	}

	logger.Info("Graph(v = %d, e = %d) loaded. Label: %s", n, len(edges), BoolToString(label))

	return NewGraph(n, edges), label
}

func BoolToString(b BoolQ) string {
	switch b {
	case TRUE:
		return "TRUE"
	case FALSE:
		return "FALSE"
	case UNKNOWN:
		return "UNKNOWN"
	default:
		return "INVALID"
	}
}
func CheckGraph(g *Graph) error {
	for _, vertex := range g.Edges {
		if g.Nodes[vertex.First] == g.Nodes[vertex.Second] {
			return fmt.Errorf("System Check: Conflict at edge (%d, %d): both nodes have the same color %b", vertex.First, vertex.Second, g.Nodes[vertex.First])
		}
	}

	logger.Info("System Check: No conflicts found in edges, checking to ensure all nodes have a valid color...")

	for i, node := range g.Nodes {
		if node != RED && node != GREEN && node != BLUE {
			return fmt.Errorf("Node %d has an invalid color: %b\n", i, node)
		}
	}

	logger.Info("System: Graph verified as validly three-colored")
	return nil
}
