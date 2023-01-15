package main
type A struct {
	a int
}
func main() {
	var a A 
	a.a = 2
	_ = a.a
}
