package main

type T struct {
	x, y int
}

func main() {
	t := new(T)
	t.x = 1
	p := &t.x
	*p = 2
}

