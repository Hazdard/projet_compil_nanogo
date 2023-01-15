package main

func foo(){
	var a = 2
	a = a + 1
}

func test(){
	_ = 2
}

func main() {
	var _ = 2
	_ = foo()
}
