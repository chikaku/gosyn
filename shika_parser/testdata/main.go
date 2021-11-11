// package comment
package testdata

import (
    "fmt"
    _ "net/http/pprof"
)

var (
    varInt    = 1
    varFloat  = 1.0
    varString = "Hello World"
)

const (
    loop = 1
)

type Mail struct {
    message string
}

func (m *Mail) Print() {
    fmt.Print(m.message)
}

func main() {
    mail := new(Mail)
    mail.message = varString
    for i := 0; i < loop; i++ {
        mail.Print()
    }
}
