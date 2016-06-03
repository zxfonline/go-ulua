// Copyright 2016 zxfonline@sina.com. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.
package ulua

import (
	"math"
	"testing"
	"unicode"
)

type Optionals struct {
	Sr string `lua:"sr"`
	So string `lua:"so,omitempty"`
	Sw string `lua:"-"`

	Ir int `lua:"omitempty"` // actually named omitempty, not an option
	Io int `lua:"io,omitempty"`

	Slr []string `lua:"slr,random"`
	Slo []string `lua:"slo,omitempty"`

	Mr map[string]interface{} `lua:"mr"`
	Mo map[string]interface{} `lua:",omitempty"`

	Fr float64 `lua:"fr"`
	Fo float64 `lua:"fo,omitempty"`

	Br bool `lua:"br"`
	Bo bool `lua:"bo,omitempty"`

	Ur uint `lua:"ur"`
	Uo uint `lua:"uo,omitempty"`

	Str struct{} `lua:"str"`
	Sto struct{} `lua:"sto,omitempty"`
}

type StringTag struct {
	BoolStr bool   `lua:",string"`
	IntStr  int64  `lua:",string"`
	StrStr  string `lua:",string"`
}

// byte slices are special even if they're renamed types.
type renamedByte byte
type renamedByteSlice []byte
type renamedRenamedByteSlice []renamedByte

func TestEncodeRenamedByteSlice(t *testing.T) {
	s := renamedByteSlice("abc")
	result, err := Marshal(s)
	if err != nil {
		t.Fatal(err)
	}
	expect := `"YWJj"`
	if string(result) != expect {
		t.Errorf(" got %s want %s", result, expect)
	}
	r := renamedRenamedByteSlice("abc")
	result, err = Marshal(r)
	if err != nil {
		t.Fatal(err)
	}
	if string(result) != expect {
		t.Errorf(" got %s want %s", result, expect)
	}
}

var unsupportedValues = []interface{}{
	math.NaN(),
	math.Inf(-1),
	math.Inf(1),
}

func TestUnsupportedValues(t *testing.T) {
	for _, v := range unsupportedValues {
		if _, err := Marshal(v); err != nil {
			if _, ok := err.(*UnsupportedValueError); !ok {
				t.Errorf("for %v, got %T want UnsupportedValueError", v, err)
			}
		} else {
			t.Errorf("for %v, expected error", v)
		}
	}
}

// RefText has Marshaler and Unmarshaler methods with pointer receiver.
type RefText int

func (*RefText) MarshalText() ([]byte, error) {
	return []byte(`"ref"`), nil
}

func (r *RefText) UnmarshalText([]byte) error {
	*r = 13
	return nil
}

// ValText has Marshaler methods with value receiver.
type ValText int

func (ValText) MarshalText() ([]byte, error) {
	return []byte(`"val"`), nil
}

func TestRefValMarshal(t *testing.T) {
	var s = struct {
		R2 RefText
		R3 *RefText
		V2 ValText
		V3 *ValText
	}{
		R2: 14,
		R3: new(RefText),
		V2: 15,
		V3: new(ValText),
	}
	const want = `{R2="\"ref\"",R3="\"ref\"",V2="\"val\"",V3="\"val\""}`
	b, err := Marshal(&s)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}
	if got := string(b); got != want {
		t.Errorf("got %q, want %q", got, want)
	}
}

// CText implements Marshaler and returns unescaped text.
type CText int

func (CText) MarshalText() ([]byte, error) {
	return []byte(`"<&>"`), nil
}

func TestMarshalerEscaping(t *testing.T) {
	var ct CText
	want := `"\"<&>\""`
	b, err := Marshal(ct)
	if err != nil {
		t.Fatalf("Marshal(ct): %v", err)
	}
	if got := string(b); got != want {
		t.Errorf("Marshal(ct) = %#q, want %#q", got, want)
	}
}

type IntType int

type MyStruct struct {
	IntType
}

func TestAnonymousNonstruct(t *testing.T) {
	var i IntType = 11
	a := MyStruct{i}
	const want = `{IntType=11}`

	b, err := Marshal(a)
	if err != nil {
		t.Fatalf("Marshal: %v", err)
	}
	if got := string(b); got != want {
		t.Errorf("got %q, want %q", got, want)
	}
}

type BugA struct {
	S string
}

type BugB struct {
	BugA
	S string
}

type BugC struct {
	S string
}

// Legal Go: We never use the repeated embedded field (S).
type BugX struct {
	A int
	BugA
	BugB
}

// Issue 5245.
func TestEmbeddedBug(t *testing.T) {
	v := BugB{
		BugA{"A"},
		"B",
	}
	b, err := Marshal(v)
	if err != nil {
		t.Fatal("Marshal:", err)
	}
	want := `{S="B"}`
	got := string(b)
	if got != want {
		t.Fatalf("Marshal: got %s want %s", got, want)
	}
	// Now check that the duplicate field, S, does not appear.
	x := BugX{
		A: 23,
	}
	b, err = Marshal(x)
	if err != nil {
		t.Fatal("Marshal:", err)
	}
	want = `{A=23}`
	got = string(b)
	if got != want {
		t.Fatalf("Marshal: got %s want %s", got, want)
	}
}

type BugD struct { // Same as BugA after tagging.
	XXX string `lua:"S"`
}

// BugD's tagged S field should dominate BugA's.
type BugY struct {
	BugA
	BugD
}

// Test that a field with a tag dominates untagged fields.
func TestTaggedFieldDominates(t *testing.T) {
	v := BugY{
		BugA{"BugA"},
		BugD{"BugD"},
	}
	b, err := Marshal(v)
	if err != nil {
		t.Fatal("Marshal:", err)
	}
	want := `{S="BugD"}`
	got := string(b)
	if got != want {
		t.Fatalf("Marshal: got %s want %s", got, want)
	}
}

// There are no tags here, so S should not appear.
type BugZ struct {
	BugA
	BugC
	BugY // Contains a tagged S field through BugD; should not dominate.
}

func TestDuplicatedFieldDisappears(t *testing.T) {
	v := BugZ{
		BugA{"BugA"},
		BugC{"BugC"},
		BugY{
			BugA{"nested BugA"},
			BugD{"nested BugD"},
		},
	}
	b, err := Marshal(v)
	if err != nil {
		t.Fatal("Marshal:", err)
	}
	want := `{}`
	got := string(b)
	if got != want {
		t.Fatalf("Marshal: got %s want %s", got, want)
	}
}

func TestStringBytes(t *testing.T) {
	// Test that encodeState.stringBytes and encodeState.string use the same encoding.
	es := &encodeState{}
	var r []rune
	for i := '\u0000'; i <= unicode.MaxRune; i++ {
		r = append(r, i)
	}
	s := string(r) + "\xff\xff\xffhello" // some invalid UTF-8 too
	es.string(s, true)

	esBytes := &encodeState{}
	esBytes.stringBytes([]byte(s), true)

	enc := es.Buffer.String()
	encBytes := esBytes.Buffer.String()
	if enc != encBytes {
		i := 0
		for i < len(enc) && i < len(encBytes) && enc[i] == encBytes[i] {
			i++
		}
		enc = enc[i:]
		encBytes = encBytes[i:]
		i = 0
		for i < len(enc) && i < len(encBytes) && enc[len(enc)-i-1] == encBytes[len(encBytes)-i-1] {
			i++
		}
		enc = enc[:len(enc)-i]
		encBytes = encBytes[:len(encBytes)-i]

		if len(enc) > 20 {
			enc = enc[:20] + "..."
		}
		if len(encBytes) > 20 {
			encBytes = encBytes[:20] + "..."
		}

		t.Errorf("encodings differ at %#q vs %#q", enc, encBytes)
	}
}

func TestIssue10281(t *testing.T) {
	type Foo struct {
		N Number
	}
	x := Foo{Number(`invalid`)}

	b, err := Marshal(&x)
	if err == nil {
		t.Errorf("Marshal(&x) = %#q; want error", b)
	}
}

var encodeStringTests = []struct {
	in  string
	out string
}{
	{"\x00", `"\u0000"`},
	{"\x01", `"\u0001"`},
	{"\x02", `"\u0002"`},
	{"\x03", `"\u0003"`},
	{"\x04", `"\u0004"`},
	{"\x05", `"\u0005"`},
	{"\x06", `"\u0006"`},
	{"\x07", `"\u0007"`},
	{"\x08", `"\u0008"`},
	{"\x09", `"\t"`},
	{"\x0a", `"\n"`},
	{"\x0b", `"\u000b"`},
	{"\x0c", `"\u000c"`},
	{"\x0d", `"\r"`},
	{"\x0e", `"\u000e"`},
	{"\x0f", `"\u000f"`},
	{"\x10", `"\u0010"`},
	{"\x11", `"\u0011"`},
	{"\x12", `"\u0012"`},
	{"\x13", `"\u0013"`},
	{"\x14", `"\u0014"`},
	{"\x15", `"\u0015"`},
	{"\x16", `"\u0016"`},
	{"\x17", `"\u0017"`},
	{"\x18", `"\u0018"`},
	{"\x19", `"\u0019"`},
	{"\x1a", `"\u001a"`},
	{"\x1b", `"\u001b"`},
	{"\x1c", `"\u001c"`},
	{"\x1d", `"\u001d"`},
	{"\x1e", `"\u001e"`},
	{"\x1f", `"\u001f"`},
}

func TestEncodeString(t *testing.T) {
	for _, tt := range encodeStringTests {
		b, err := Marshal(tt.in)
		if err != nil {
			t.Errorf("Marshal(%q): %v", tt.in, err)
			continue
		}
		out := string(b)
		if out != tt.out {
			t.Errorf("Marshal(%q) = %#q, want %#q", tt.in, out, tt.out)
		}
	}
}
