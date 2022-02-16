/*
Copyright 2014 Google Inc. All rights reserved.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

package fuzz

import (
	"fmt"
	"math/rand"
	"reflect"
	"regexp"
	"sync"
	"time"
	"unsafe"

	"strings"

	"github.com/google/gofuzz/bytesource"
)

// A Source represents a source of uniformly-distributed
// pseudo-random int64 values in the range [0, 1<<63).
type RandProxySource interface {
	Int63() int64
	Seed(seed int64)
	Failed() bool
}

type RandProxySource64 interface {
	RandProxySource
	Uint64() uint64
}

// A Rand is a source of random numbers.
type RandProxy struct {
	src    RandProxySource
	s64    RandProxySource64 // non-nil if src is source64

	// readVal contains remainder of 63-bit integer used for bytes
	// generation during most recent Read call.
	// It is saved so next Read call can start where the previous
	// one finished.
	readVal int64
	// readPos indicates the number of low-order bytes of readVal
	// that are still valid.
	readPos int8
}

// New returns a new Rand that uses random values from src
// to generate other random values.
func NewRandProxy(src RandProxySource) *RandProxy {
	s64, _ := src.(RandProxySource64)
	return &RandProxy{src: src, s64: s64}
}

// Intn returns, as an int, a non-negative pseudo-random number in the half-open interval [0,n).
// It panics if n <= 0.
func (r *RandProxy) Intn(n int) int {
	if n <= 0 {
		panic("invalid argument to Intn")
	}
	if n <= 1<<31-1 {
		return int(r.Int31n(int32(n)))
	}
	return int(r.Int63n(int64(n)))
}

// Int63n returns, as an int64, a non-negative pseudo-random number in the half-open interval [0,n).
// It panics if n <= 0.
func (r *RandProxy) Int63n(n int64) int64 {
	if n <= 0 {
		panic("invalid argument to Int63n")
	}
	if n&(n-1) == 0 { // n is power of two, can mask
		return r.Int63() & (n - 1)
	}
	max := int64((1 << 63) - 1 - (1<<63)%uint64(n))
	v := r.Int63()
	for v > max {
		v = r.Int63()
	}
	return v % n
}

// Int63 returns a non-negative pseudo-random 63-bit integer as an int64.
func (r *RandProxy) Int63() int64 { return r.src.Int63() }

// Int31 returns a non-negative pseudo-random 31-bit integer as an int32.
func (r *RandProxy) Int31() int32 { return int32(r.Int63() >> 32) }

// Float64 returns, as a float64, a pseudo-random number in the half-open interval [0.0,1.0).
func (r *RandProxy) Float64() float64 {
	// A clearer, simpler implementation would be:
	//	return float64(r.Int63n(1<<53)) / (1<<53)
	// However, Go 1 shipped with
	//	return float64(r.Int63()) / (1 << 63)
	// and we want to preserve that value stream.
	//
	// There is one bug in the value stream: r.Int63() may be so close
	// to 1<<63 that the division rounds up to 1.0, and we've guaranteed
	// that the result is always less than 1.0.
	//
	// We tried to fix this by mapping 1.0 back to 0.0, but since float64
	// values near 0 are much denser than near 1, mapping 1 to 0 caused
	// a theoretically significant overshoot in the probability of returning 0.
	// Instead of that, if we round up to 1, just try again.
	// Getting 1 only happens 1/2⁵³ of the time, so most clients
	// will not observe it anyway.
again:
	f := float64(r.Int63()) / (1 << 63)
	if f == 1 {
		goto again // resample; this branch is taken O(never)
	}
	return f
}

// Int31n returns, as an int32, a non-negative pseudo-random number in the half-open interval [0,n).
// It panics if n <= 0.
func (r *RandProxy) Int31n(n int32) int32 {
	if n <= 0 {
		panic("invalid argument to Int31n")
	}
	if n&(n-1) == 0 { // n is power of two, can mask
		return r.Int31() & (n - 1)
	}
	max := int32((1 << 31) - 1 - (1<<31)%uint32(n))
	v := r.Int31()
	for v > max {
		v = r.Int31()
	}
	return v % n
}

// Float32 returns, as a float32, a pseudo-random number in the half-open interval [0.0,1.0).
func (r *RandProxy) Float32() float32 {
	// Same rationale as in Float64: we want to preserve the Go 1 value
	// stream except we want to fix it not to return 1.0
	// This only happens 1/2²⁴ of the time (plus the 1/2⁵³ of the time in Float64).
again:
	f := float32(r.Float64())
	if f == 1 {
		goto again // resample; this branch is taken O(very rarely)
	}
	return f
}

// Uint32 returns a pseudo-random 32-bit value as a uint32.
func (r *RandProxy) Uint32() uint32 { return uint32(r.Int63() >> 31) }

// fuzzFuncMap is a map from a type to a fuzzFunc that handles that type.
type fuzzFuncMap map[reflect.Type]reflect.Value

// Fuzzer knows how to fill any object with random fields.
type Fuzzer struct {
	fuzzFuncs             fuzzFuncMap
	defaultFuzzFuncs      fuzzFuncMap
	r                     *RandProxy
	nilChance             float64
	minElements           int
	maxElements           int
	maxDepth              int
	allowUnexportedFields bool
	skipFieldPatterns     []*regexp.Regexp

	fuzzLock sync.Mutex
}

// New returns a new Fuzzer. Customize your Fuzzer further by calling Funcs,
// RandSource, NilChance, or NumElements in any order.
func New() *Fuzzer {
	return NewWithSeed(time.Now().UnixNano())
}

func NewWithSeed(seed int64) *Fuzzer {
	dummy_data := []byte{0, 0, 0, 0}
	f := &Fuzzer{
		defaultFuzzFuncs: fuzzFuncMap{
			reflect.TypeOf(&time.Time{}): reflect.ValueOf(fuzzTime),
		},

		fuzzFuncs:             fuzzFuncMap{},
		r:                     NewRandProxy(bytesource.New(dummy_data)),
		nilChance:             .2,
		minElements:           1,
		maxElements:           10,
		maxDepth:              100,
		allowUnexportedFields: false,
	}
	return f
}

func (f *Fuzzer) IsDataFinished() bool {
	if f.r.src.Failed() == true {
		return true
	}
	return false
}

// NewFromGoFuzz is a helper function that enables using gofuzz (this
// project) with go-fuzz (https://github.com/dvyukov/go-fuzz) for continuous
// fuzzing. Essentially, it enables translating the fuzzing bytes from
// go-fuzz to any Go object using this library.
//
// This implementation promises a constant translation from a given slice of
// bytes to the fuzzed objects. This promise will remain over future
// versions of Go and of this library.
//
// Note: the returned Fuzzer should not be shared between multiple goroutines,
// as its deterministic output will no longer be available.
//
// Example: use go-fuzz to test the function `MyFunc(int)` in the package
// `mypackage`. Add the file: "mypacakge_fuzz.go" with the content:
//
// // +build gofuzz
// package mypacakge
// import fuzz "github.com/infosecual/gofuzz"
// func Fuzz(data []byte) int {
// 	var i int
// 	fuzz.NewFromGoFuzz(data).Fuzz(&i)
// 	MyFunc(i)
// 	return 0
// }
func NewFromGoFuzz(data []byte) *Fuzzer {
	return New().RandSource(bytesource.New(data))
}

// Funcs adds each entry in fuzzFuncs as a custom fuzzing function.
//
// Each entry in fuzzFuncs must be a function taking two parameters.
// The first parameter must be a pointer or map. It is the variable that
// function will fill with random data. The second parameter must be a
// fuzz.Continue, which will provide a source of randomness and a way
// to automatically continue fuzzing smaller pieces of the first parameter.
//
// These functions are called sensibly, e.g., if you wanted custom string
// fuzzing, the function `func(s *string, c fuzz.Continue)` would get
// called and passed the address of strings. Maps and pointers will always
// be made/new'd for you, ignoring the NilChange option. For slices, it
// doesn't make much sense to  pre-create them--Fuzzer doesn't know how
// long you want your slice--so take a pointer to a slice, and make it
// yourself. (If you don't want your map/pointer type pre-made, take a
// pointer to it, and make it yourself.) See the examples for a range of
// custom functions.
func (f *Fuzzer) Funcs(fuzzFuncs ...interface{}) *Fuzzer {
	for i := range fuzzFuncs {
		v := reflect.ValueOf(fuzzFuncs[i])
		if v.Kind() != reflect.Func {
			panic("Need only funcs!")
		}
		t := v.Type()
		if t.NumIn() != 2 || t.NumOut() != 0 {
			panic("Need 2 in and 0 out params!")
		}
		argT := t.In(0)
		switch argT.Kind() {
		case reflect.Ptr, reflect.Map:
		default:
			panic("fuzzFunc must take pointer or map type")
		}
		if t.In(1) != reflect.TypeOf(Continue{}) {
			panic("fuzzFunc's second parameter must be type fuzz.Continue")
		}
		f.fuzzFuncs[argT] = v
	}
	return f
}

// RandSource causes f to get values from the given source of randomness.
// Use if you want deterministic fuzzing.
func (f *Fuzzer) RandSource(s RandProxySource) *Fuzzer {
	f.r = NewRandProxy(s)
	return f
}

// NilChance sets the probability of creating a nil pointer, map, or slice to
// 'p'. 'p' should be between 0 (no nils) and 1 (all nils), inclusive.
func (f *Fuzzer) NilChance(p float64) *Fuzzer {
	if p < 0 || p > 1 {
		panic("p should be between 0 and 1, inclusive.")
	}
	f.nilChance = p
	return f
}

// NumElements sets the minimum and maximum number of elements that will be
// added to a non-nil map or slice.
func (f *Fuzzer) NumElements(atLeast, atMost int) *Fuzzer {
	if atLeast > atMost {
		panic("atLeast must be <= atMost")
	}
	if atLeast < 0 {
		panic("atLeast must be >= 0")
	}
	f.minElements = atLeast
	f.maxElements = atMost
	return f
}

func (f *Fuzzer) genElementCount() int {
	if f.minElements == f.maxElements {
		return f.minElements
	}
	return f.minElements + f.r.Intn(f.maxElements-f.minElements+1)
}

func (f *Fuzzer) genShouldFill() bool {
	return f.r.Float64() >= f.nilChance
}

// MaxDepth sets the maximum number of recursive fuzz calls that will be made
// before stopping.  This includes struct members, pointers, and map and slice
// elements.
func (f *Fuzzer) MaxDepth(d int) *Fuzzer {
	f.maxDepth = d
	return f
}

// AllowUnexportedFields decides whether to do fuzz on the unexported fields,
// i.e. the fields that start with lower case letter.
func (f *Fuzzer) AllowUnexportedFields(flag bool) *Fuzzer {
	f.allowUnexportedFields = flag
	return f
}

// SkipFieldsWithPattern Skip fields which match the supplied pattern. Call this multiple times if needed
// This is useful to skip XXX_ fields generated by protobuf
func (f *Fuzzer) SkipFieldsWithPattern(pattern *regexp.Regexp) *Fuzzer {
	f.skipFieldPatterns = append(f.skipFieldPatterns, pattern)
	return f
}

// Fuzz recursively fills all of obj's fields with something random.  First
// this tries to find a custom fuzz function (see Funcs).  If there is no
// custom function this tests whether the object implements fuzz.Interface and,
// if so, calls Fuzz on it to fuzz itself.  If that fails, this will see if
// there is a default fuzz function provided by this package.  If all of that
// fails, this will generate random values for all primitive fields and then
// recurse for all non-primitives.
//
// This is safe for cyclic or tree-like structs, up to a limit.  Use the
// MaxDepth method to adjust how deep you need it to recurse.
//
// obj must be a pointer. Only exported (public) fields can be set (thanks,
// golang :/ ) Intended for tests, so will panic on bad input or unimplemented
// fields.
func (f *Fuzzer) Fuzz(obj interface{}) {
	f.fuzzLock.Lock()
	defer f.fuzzLock.Unlock()

	v := reflect.ValueOf(obj)
	if v.Kind() != reflect.Ptr {
		panic("needed ptr!")
	}
	v = v.Elem()
	f.fuzzWithContext(v, 0)
}

// FuzzNoCustom is just like Fuzz, except that any custom fuzz function for
// obj's type will not be called and obj will not be tested for fuzz.Interface
// conformance.  This applies only to obj and not other instances of obj's
// type.
// Not safe for cyclic or tree-like structs!
// obj must be a pointer. Only exported (public) fields can be set (thanks, golang :/ )
// Intended for tests, so will panic on bad input or unimplemented fields.
func (f *Fuzzer) FuzzNoCustom(obj interface{}) {
	f.fuzzLock.Lock()
	defer f.fuzzLock.Unlock()

	v := reflect.ValueOf(obj)
	if v.Kind() != reflect.Ptr {
		panic("needed ptr!")
	}
	v = v.Elem()
	f.fuzzWithContext(v, flagNoCustomFuzz)
}

const (
	// Do not try to find a custom fuzz function.  Does not apply recursively.
	flagNoCustomFuzz uint64 = 1 << iota
)

func (f *Fuzzer) fuzzWithContext(v reflect.Value, flags uint64) {
	fc := &fuzzerContext{fuzzer: f}
	fc.doFuzz(v, flags)
}

// fuzzerContext carries context about a single fuzzing run, which lets Fuzzer
// be thread-safe.
type fuzzerContext struct {
	fuzzer   *Fuzzer
	curDepth int
}

func (fc *fuzzerContext) doFuzz(v reflect.Value, flags uint64) {
	if fc.curDepth >= fc.fuzzer.maxDepth {
		return
	}
	fc.curDepth++
	defer func() { fc.curDepth-- }()

	if !v.CanSet() {
		if !fc.fuzzer.allowUnexportedFields || !v.CanAddr() {
			return
		}
		v = reflect.NewAt(v.Type(), unsafe.Pointer(v.UnsafeAddr())).Elem()
	}

	if flags&flagNoCustomFuzz == 0 {
		// Check for both pointer and non-pointer custom functions.
		if v.CanAddr() && fc.tryCustom(v.Addr()) {
			return
		}
		if fc.tryCustom(v) {
			return
		}
	}

	if fn, ok := fillFuncMap[v.Kind()]; ok {
		fn(v, fc.fuzzer.r)
		return
	}

	switch v.Kind() {
	case reflect.Map:
		if fc.fuzzer.genShouldFill() {
			v.Set(reflect.MakeMap(v.Type()))
			n := fc.fuzzer.genElementCount()
			for i := 0; i < n; i++ {
				key := reflect.New(v.Type().Key()).Elem()
				fc.doFuzz(key, 0)
				val := reflect.New(v.Type().Elem()).Elem()
				fc.doFuzz(val, 0)
				v.SetMapIndex(key, val)
			}
			return
		}
		v.Set(reflect.Zero(v.Type()))
	case reflect.Ptr:
		if fc.fuzzer.genShouldFill() {
			v.Set(reflect.New(v.Type().Elem()))
			fc.doFuzz(v.Elem(), 0)
			return
		}
		v.Set(reflect.Zero(v.Type()))
	case reflect.Slice:
		if fc.fuzzer.genShouldFill() {
			n := fc.fuzzer.genElementCount()
			v.Set(reflect.MakeSlice(v.Type(), n, n))
			for i := 0; i < n; i++ {
				fc.doFuzz(v.Index(i), 0)
			}
			return
		}
		v.Set(reflect.Zero(v.Type()))
	case reflect.Array:
		if fc.fuzzer.genShouldFill() {
			n := v.Len()
			for i := 0; i < n; i++ {
				fc.doFuzz(v.Index(i), 0)
			}
			return
		}
		v.Set(reflect.Zero(v.Type()))
	case reflect.Struct:
		for i := 0; i < v.NumField(); i++ {
			skipField := false
			fieldName := v.Type().Field(i).Name
			for _, pattern := range fc.fuzzer.skipFieldPatterns {
				if pattern.MatchString(fieldName) {
					skipField = true
					break
				}
			}
			if !skipField {
				fc.doFuzz(v.Field(i), 0)
			}
		}
	case reflect.Chan:
		fallthrough
	case reflect.Func:
		fallthrough
	case reflect.Interface:
		fallthrough
	default:
		panic(fmt.Sprintf("Can't handle %#v", v.Interface()))
	}
}

// tryCustom searches for custom handlers, and returns true iff it finds a match
// and successfully randomizes v.
func (fc *fuzzerContext) tryCustom(v reflect.Value) bool {
	// First: see if we have a fuzz function for it.
	doCustom, ok := fc.fuzzer.fuzzFuncs[v.Type()]
	if !ok {
		// Second: see if it can fuzz itself.
		if v.CanInterface() {
			intf := v.Interface()
			if fuzzable, ok := intf.(Interface); ok {
				fuzzable.Fuzz(Continue{fc: fc, RandProxy: fc.fuzzer.r})
				return true
			}
		}
		// Finally: see if there is a default fuzz function.
		doCustom, ok = fc.fuzzer.defaultFuzzFuncs[v.Type()]
		if !ok {
			return false
		}
	}

	switch v.Kind() {
	case reflect.Ptr:
		if v.IsNil() {
			if !v.CanSet() {
				return false
			}
			v.Set(reflect.New(v.Type().Elem()))
		}
	case reflect.Map:
		if v.IsNil() {
			if !v.CanSet() {
				return false
			}
			v.Set(reflect.MakeMap(v.Type()))
		}
	default:
		return false
	}

	doCustom.Call([]reflect.Value{v, reflect.ValueOf(Continue{
		fc:   fc,
		RandProxy: fc.fuzzer.r,
	})})
	return true
}

// Interface represents an object that knows how to fuzz itself.  Any time we
// find a type that implements this interface we will delegate the act of
// fuzzing itself.
type Interface interface {
	Fuzz(c Continue)
}

// Continue can be passed to custom fuzzing functions to allow them to use
// the correct source of randomness and to continue fuzzing their members.
type Continue struct {
	fc *fuzzerContext

	// For convenience, Continue implements rand.Rand via embedding.
	// Use this for generating any randomness if you want your fuzzing
	// to be repeatable for a given seed.
	*RandProxy
	*rand.Rand
}

// Fuzz continues fuzzing obj. obj must be a pointer or a reflect.Value of a
// pointer.
func (c Continue) Fuzz(obj interface{}) {
	v, ok := obj.(reflect.Value)
	if !ok {
		v = reflect.ValueOf(obj)
	}
	if v.Kind() != reflect.Ptr {
		panic("needed ptr!")
	}
	v = v.Elem()
	c.fc.doFuzz(v, 0)
}

// FuzzNoCustom continues fuzzing obj, except that any custom fuzz function for
// obj's type will not be called and obj will not be tested for fuzz.Interface
// conformance.  This applies only to obj and not other instances of obj's
// type.
func (c Continue) FuzzNoCustom(obj interface{}) {
	v, ok := obj.(reflect.Value)
	if !ok {
		v = reflect.ValueOf(obj)
	}
	if v.Kind() != reflect.Ptr {
		panic("needed ptr!")
	}
	v = v.Elem()
	c.fc.doFuzz(v, flagNoCustomFuzz)
}

// RandString makes a random string up to 20 characters long. The returned string
// may include a variety of (valid) UTF-8 encodings.
func (c Continue) RandString() string {
	return randString(c.RandProxy)
}

// RandUint64 makes random 64 bit numbers.
// Weirdly, rand doesn't have a function that gives you 64 random bits.
func (c Continue) RandUint64() uint64 {
	return randUint64(c.RandProxy)
}

// RandBool returns true or false randomly.
func (c Continue) RandBool() bool {
	return randBool(c.RandProxy)
}

func fuzzInt(v reflect.Value, r *RandProxy) {
	v.SetInt(int64(randUint64(r)))
}

func fuzzUint(v reflect.Value, r *RandProxy) {
	v.SetUint(randUint64(r))
}

func fuzzTime(t *time.Time, c Continue) {
	var sec, nsec int64
	// Allow for about 1000 years of random time values, which keeps things
	// like JSON parsing reasonably happy.
	sec = c.RandProxy.Int63n(1000 * 365 * 24 * 60 * 60)
	c.Fuzz(&nsec)
	*t = time.Unix(sec, nsec)
}

var fillFuncMap = map[reflect.Kind]func(reflect.Value, *RandProxy){
	reflect.Bool: func(v reflect.Value, r *RandProxy) {
		v.SetBool(randBool(r))
	},
	reflect.Int:     fuzzInt,
	reflect.Int8:    fuzzInt,
	reflect.Int16:   fuzzInt,
	reflect.Int32:   fuzzInt,
	reflect.Int64:   fuzzInt,
	reflect.Uint:    fuzzUint,
	reflect.Uint8:   fuzzUint,
	reflect.Uint16:  fuzzUint,
	reflect.Uint32:  fuzzUint,
	reflect.Uint64:  fuzzUint,
	reflect.Uintptr: fuzzUint,
	reflect.Float32: func(v reflect.Value, r *RandProxy) {
		v.SetFloat(float64(r.Float32()))
	},
	reflect.Float64: func(v reflect.Value, r *RandProxy) {
		v.SetFloat(r.Float64())
	},
	reflect.Complex64: func(v reflect.Value, r *RandProxy) {
		v.SetComplex(complex128(complex(r.Float32(), r.Float32())))
	},
	reflect.Complex128: func(v reflect.Value, r *RandProxy) {
		v.SetComplex(complex(r.Float64(), r.Float64()))
	},
	reflect.String: func(v reflect.Value, r *RandProxy) {
		v.SetString(randString(r))
	},
	reflect.UnsafePointer: func(v reflect.Value, r *RandProxy) {
		panic("unimplemented")
	},
}

// randBool returns true or false randomly.
func randBool(r *RandProxy) bool {
	return r.Int31()&(1<<30) == 0
}

type int63nPicker interface {
	Int63n(int64) int64
}

// UnicodeRange describes a sequential range of unicode characters.
// Last must be numerically greater than First.
type UnicodeRange struct {
	First, Last rune
}

// UnicodeRanges describes an arbitrary number of sequential ranges of unicode characters.
// To be useful, each range must have at least one character (First <= Last) and
// there must be at least one range.
type UnicodeRanges []UnicodeRange

// choose returns a random unicode character from the given range, using the
// given randomness source.
func (ur UnicodeRange) choose(r int63nPicker) rune {
	count := int64(ur.Last - ur.First + 1)
	return ur.First + rune(r.Int63n(count))
}

// CustomStringFuzzFunc constructs a FuzzFunc which produces random strings.
// Each character is selected from the range ur. If there are no characters
// in the range (cr.Last < cr.First), this will panic.
func (ur UnicodeRange) CustomStringFuzzFunc() func(s *string, c Continue) {
	ur.check()
	return func(s *string, c Continue) {
		*s = ur.randString(c.RandProxy)
	}
}

// check is a function that used to check whether the first of ur(UnicodeRange)
// is greater than the last one.
func (ur UnicodeRange) check() {
	if ur.Last < ur.First {
		panic("The last encoding must be greater than the first one.")
	}
}

// randString of UnicodeRange makes a random string up to 20 characters long.
// Each character is selected form ur(UnicodeRange).
func (ur UnicodeRange) randString(r *RandProxy) string {
	n := r.Intn(20)
	sb := strings.Builder{}
	sb.Grow(n)
	for i := 0; i < n; i++ {
		sb.WriteRune(ur.choose(r))
	}
	return sb.String()
}

// defaultUnicodeRanges sets a default unicode range when user do not set
// CustomStringFuzzFunc() but wants fuzz string.
var defaultUnicodeRanges = UnicodeRanges{
	{' ', '~'},           // ASCII characters
	{'\u00a0', '\u02af'}, // Multi-byte encoded characters
	{'\u4e00', '\u9fff'}, // Common CJK (even longer encodings)
}

// CustomStringFuzzFunc constructs a FuzzFunc which produces random strings.
// Each character is selected from one of the ranges of ur(UnicodeRanges).
// Each range has an equal probability of being chosen. If there are no ranges,
// or a selected range has no characters (.Last < .First), this will panic.
// Do not modify any of the ranges in ur after calling this function.
func (ur UnicodeRanges) CustomStringFuzzFunc() func(s *string, c Continue) {
	// Check unicode ranges slice is empty.
	if len(ur) == 0 {
		panic("UnicodeRanges is empty.")
	}
	// if not empty, each range should be checked.
	for i := range ur {
		ur[i].check()
	}
	return func(s *string, c Continue) {
		*s = ur.randString(c.RandProxy)
	}
}

// randString of UnicodeRanges makes a random string up to 20 characters long.
// Each character is selected form one of the ranges of ur(UnicodeRanges),
// and each range has an equal probability of being chosen.
func (ur UnicodeRanges) randString(r *RandProxy) string {
	n := r.Intn(20)
	sb := strings.Builder{}
	sb.Grow(n)
	for i := 0; i < n; i++ {
		sb.WriteRune(ur[r.Intn(len(ur))].choose(r))
	}
	return sb.String()
}

// randString makes a random string up to 20 characters long. The returned string
// may include a variety of (valid) UTF-8 encodings.
func randString(r *RandProxy) string {
	return defaultUnicodeRanges.randString(r)
}

// randUint64 makes random 64 bit numbers.
// Weirdly, rand doesn't have a function that gives you 64 random bits.
func randUint64(r *RandProxy) uint64 {
	return uint64(r.Uint32())<<32 | uint64(r.Uint32())
}
