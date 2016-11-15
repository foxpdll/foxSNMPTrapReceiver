package main

import (
        "errors"
        "fmt"
        "net"
        "net/http"
        "sort"
        "strconv"
        "strings"
        "sync"
        "time"
)

const (
        Integer                    Asn1BER = 0x02
        BitString                          = 0x03
        OctetString                        = 0x04
        Null                               = 0x05
        ObjectIdentifier                   = 0x06
        Sequence                           = 0x30
        IpAddress                          = 0x40
        Counter32                          = 0x41
        Gauge32                            = 0x42
        TimeTicks                          = 0x43
        Opaque                             = 0x44
        NsapAddress                        = 0x45
        Counter64                          = 0x46
        Uinteger32                         = 0x47
        NoSuchObject                       = 0x80
        NoSuchInstance                     = 0x81
        GetRequest                         = 0xa0
        GetNextRequest                     = 0xa1
        GetResponse                        = 0xa2
        SetRequest                         = 0xa3
        Trap                               = 0xa4
        GetBulkRequest                     = 0xa5
        TrapV2                             = 0xa7
        EndOfMibView                       = 0x82
        snmp_coldStart                     = ".1.3.6.1.6.3.1.1.5.1"
        snmp_warmStart                     = ".1.3.6.1.6.3.1.1.5.2"
        snmp_linkDown                      = ".1.3.6.1.6.3.1.1.5.3"
        snmp_linkUp                        = ".1.3.6.1.6.3.1.1.5.4"
        snmp_authenticationFailure         = ".1.3.6.1.6.3.1.1.5.5"
        snmp_egpNeighborLoss               = ".1.3.6.1.6.3.1.1.5.6"
        snmp_enterpriseSpecific            = ".1.3.6.1.6.3.1.1.5.7"
)

type Asn1BER byte

type SnmpPDU struct {
        Name  string
        Type  Asn1BER
        Value interface{}
}

type FoxSNMP struct {
        Version      string
        Community    string
        id           int
        error_status int
        error_index  int
        uptime       int
        Variables    []SnmpPDU
}

type Variable struct {
        Name  []int
        Type  Asn1BER
        Size  uint64
        Value interface{}
}

type RawBER struct {
        Type         Asn1BER
        HeaderLength uint64
        DataLength   uint64
        Data         []byte
        BERVariable  *Variable
}

type Pair struct {
        Key   string
        Value int
}

type PairList []Pair

func (p PairList) Len() int           { return len(p) }
func (p PairList) Less(i, j int) bool { return p[i].Value < p[j].Value }
func (p PairList) Swap(i, j int)      { p[i], p[j] = p[j], p[i] }

func foxSort(a map[string]int) PairList {
        pl := make(PairList, len(a))
        i := 0
        for k, v := range a {
                pl[i] = Pair{k, v}
                i++
        }
        sort.Sort(sort.Reverse(pl))
        return pl
}

func Uvarint(buf []byte) (x uint64) {
        for i, b := range buf {
                x = x<<8 + uint64(b)
                if i == 7 {
                        return
                }
        }
        return
}

// parseInt treats the given bytes as a big-endian, signed integer and returns
// the result.
func parseInt(bytes []byte) (int, error) {
        ret64, err := parseInt64(bytes)
        if err != nil {
                return 0, err
        }
        if ret64 != int64(int(ret64)) {
                return 0, errors.New("integer too large")
        }
        return int(ret64), nil
}

// parseInt64 treats the given bytes as a big-endian, signed integer and
// returns the result.
func parseInt64(bytes []byte) (ret int64, err error) {
        if len(bytes) > 8 {
                // We'll overflow an int64 in this case.
                err = errors.New("integer too large")
                return
        }
        for bytesRead := 0; bytesRead < len(bytes); bytesRead++ {
                ret <<= 8
                ret |= int64(bytes[bytesRead])
        }

        // Shift up and down in order to sign extend the result.
        ret <<= 64 - uint8(len(bytes))*8
        ret >>= 64 - uint8(len(bytes))*8
        return
}

// parseObjectIdentifier parses an OBJECT IDENTIFIER from the given bytes and
// returns it. An object identifier is a sequence of variable length integers
// that are assigned in a hierarchy.
func parseObjectIdentifier(bytes []byte) (s []int, err error) {
        if len(bytes) == 0 {
                err = fmt.Errorf("zero length OBJECT IDENTIFIER")
                return
        }

        // In the worst case, we get two elements from the first byte (which is
        // encoded differently) and then every varint is a single byte long.
        s = make([]int, len(bytes)+1)

        // The first byte is 40*value1 + value2:
        s[0] = int(bytes[0]) / 40
        s[1] = int(bytes[0]) % 40
        i := 2
        for offset := 1; offset < len(bytes); i++ {
                var v int
                v, offset, err = parseBase128Int(bytes, offset)
                if err != nil {
                        return
                }
                s[i] = v
        }
        s = s[0:i]
        return
}

// parseBase128Int parses a base-128 encoded int from the given offset in the
// given byte slice. It returns the value and the new offset.
func parseBase128Int(bytes []byte, initOffset int) (ret, offset int, err error) {
        offset = initOffset
        for shifted := 0; offset < len(bytes); shifted++ {
                if shifted > 4 {
                        err = fmt.Errorf("Structural Error: base 128 integer too large")
                        return
                }
                ret <<= 7
                b := bytes[offset]
                ret |= int(b & 0x7f)
                offset++
                if b&0x80 == 0 {
                        return
                }
        }
        err = fmt.Errorf("Syntax Error: truncated base 128 integer")
        return
}

func decodeValue(valueType Asn1BER, data []byte) (retVal *Variable, err error) {
        retVal = new(Variable)
        retVal.Size = uint64(len(data))

        switch Asn1BER(valueType) {

        // Integer
        case Integer:
                ret, err := parseInt(data)
                if err != nil {
                        break
                }
                retVal.Type = Integer
                retVal.Value = ret
        // Octet
        case OctetString:
                retVal.Type = OctetString
                retVal.Value = string(data)
        case ObjectIdentifier:
                retVal.Type = ObjectIdentifier
                retVal.Value, _ = parseObjectIdentifier(data)
        // IpAddress
        case IpAddress:
                retVal.Type = IpAddress
                retVal.Value = net.IP{data[0], data[1], data[2], data[3]}
        // Counter32
        case Counter32:
                ret := Uvarint(data)
                retVal.Type = Counter32
                retVal.Value = ret
        case TimeTicks:
                ret, err := parseInt(data)
                if err != nil {
                        break
                }
                retVal.Type = TimeTicks
                retVal.Value = ret
        // Gauge32
        case Gauge32:
                ret := Uvarint(data)
                retVal.Type = Gauge32
                retVal.Value = ret
        case Counter64:
                ret := Uvarint(data)
                retVal.Type = Counter64
                retVal.Value = ret
        case Null:
                retVal.Value = nil
        case Sequence:
                // NOOP
                retVal.Value = data
        case TrapV2:
                // NOOP
                retVal.Value = data
        case GetResponse:
                // NOOP
                retVal.Value = data
        case GetRequest:
                // NOOP
                retVal.Value = data
        case EndOfMibView:
                retVal.Type = EndOfMibView
                retVal.Value = "endOfMib"
        case GetBulkRequest:
                // NOOP
                retVal.Value = data
        case NoSuchInstance:
                return nil, fmt.Errorf("No such instance")
        case NoSuchObject:
                return nil, fmt.Errorf("No such object")
        default:
                err = fmt.Errorf("Unable to decode %s %#v - not implemented", valueType, valueType)
        }

        return retVal, err
}

func parseField(data []byte) (*RawBER, error) {
        var err error

        if len(data) == 0 {
                return nil, fmt.Errorf("Unable to parse BER: Data length 0")
        }

        ber := new(RawBER)

        ber.Type = Asn1BER(data[0])

        // Parse Length
        length := data[1]

        // Check if this is padded or not
        if length > 0x80 {
                length = length - 0x80
                ber.DataLength = Uvarint(data[2 : 2+length])
                ber.HeaderLength = 2 + uint64(length)
        } else {
                ber.HeaderLength = 2
                ber.DataLength = uint64(length)
        }

        // Do sanity checks
        if ber.DataLength > uint64(len(data)) {
                return nil, fmt.Errorf("Unable to parse BER: provided data length is longer than actual data (%d vs %d)", ber.DataLength, len(data))
        }

        ber.Data = data[ber.HeaderLength : ber.HeaderLength+ber.DataLength]

        ber.BERVariable, err = decodeValue(ber.Type, ber.Data)

        if err != nil {
                return nil, fmt.Errorf("Unable to decode value: %s\n", err.Error())
        }

        return ber, nil
}

func oidToString(oid []int) (ret string) {
        values := make([]interface{}, len(oid))
        for i, v := range oid {
                values[i] = v
        }
        return fmt.Sprintf(strings.Repeat(".%d", len(oid)), values...)
}

func checkError(err error) {
        if err != nil {
                panic(err)
        }
}

func snmpParse(packet []byte) *FoxSNMP {
        var cursor uint64 = 0

        resp := new(FoxSNMP)
        resp.Variables = make([]SnmpPDU, 0, 5)

        if Asn1BER(packet[0]) == Sequence {
                ber, err := parseField(packet)
                checkError(err)
                cursor += ber.HeaderLength

                rawVersion, err := parseField(packet[cursor:])
                checkError(err)
                cursor += rawVersion.DataLength + rawVersion.HeaderLength

                rawCommunity, err := parseField(packet[cursor:])
                checkError(err)
                cursor += rawCommunity.DataLength + rawCommunity.HeaderLength

                resp.Community = rawCommunity.BERVariable.Value.(string)

                //              fmt.Println(rawVersion.Data[0])
                //              fmt.Println(resp.Community)

                if rawVersion.Data[0] == 0 { //SNMPv1
                        resp.Version = "1"
                }

                if rawVersion.Data[0] == 1 { //SNMPv2
                        resp.Version = "v2c"

                        rawPDU, err := parseField(packet[cursor:])
                        checkError(err)
                        cursor += rawPDU.HeaderLength

                        //                      fmt.Println(rawCommunity.BERVariable.Value.(string))
                        //                      fmt.Println(rawVersion.Data)
                        //                      fmt.Println(rawPDU.Type)
                        switch rawPDU.Type {
                        default:
                        case TrapV2:
                                rawRequestId, err := parseField(packet[cursor:])
                                cursor += rawRequestId.DataLength + rawRequestId.HeaderLength
                                checkError(err)

                                rawError, err := parseField(packet[cursor:])
                                cursor += rawError.DataLength + rawError.HeaderLength
                                checkError(err)

                                rawErrorIndex, err := parseField(packet[cursor:])
                                cursor += rawErrorIndex.DataLength + rawErrorIndex.HeaderLength
                                checkError(err)

                                rawResp, err := parseField(packet[cursor:])
                                cursor += rawResp.HeaderLength
                                checkError(err)

                                resp.id = rawRequestId.BERVariable.Value.(int)
                                resp.error_status = rawError.BERVariable.Value.(int)
                                resp.error_index = rawErrorIndex.BERVariable.Value.(int)

                                for cursor < uint64(len(packet)) {
                                        rawVarbind, err := parseField(packet[cursor:])
                                        cursor += rawVarbind.HeaderLength
                                        checkError(err)

                                        rawOid, err := parseField(packet[cursor:])
                                        cursor += rawOid.HeaderLength + rawOid.DataLength
                                        checkError(err)

                                        rawValue, err := parseField(packet[cursor:])
                                        cursor += rawValue.HeaderLength + rawValue.DataLength
                                        checkError(err)

                                        if rawValue.Type == 6 {
                                                resp.Variables = append(resp.Variables, SnmpPDU{oidToString(rawOid.BERVariable.Value.([]int)), rawValue.Type, oidToString(rawValue.BERVariable.Value.([]int))})
                                        } else {
                                                resp.Variables = append(resp.Variables, SnmpPDU{oidToString(rawOid.BERVariable.Value.([]int)), rawValue.Type, rawValue.BERVariable.Value})
                                        }

                                        //fmt.Println(oidToString(rawOid.BERVariable.Value.([]int)))
                                        //fmt.Println(rawValue.Type)
                                        //fmt.Println(rawValue.BERVariable.Value)
                                        //fmt.Println("111111111111111111111111111111111111111111111111111111")

                                        //if oid, ok := rawOid.BERVariable.Value.([]int); ok {
                                        //response.Variables = append(response.Variables, SnmpPDU{oidToString(oid), rawValue.Type, rawValue.BERVariable.Value})
                                        //}

                                }

                                //                              fmt.Println(rawRequestId.BERVariable.Value.(int))
                                //                              fmt.Println(rawError.BERVariable.Value.(int))
                                //                              fmt.Println(rawErrorIndex.BERVariable.Value.(int))
                                //                              fmt.Println(rawResp.Type)

                        }

                }

                if rawVersion.Data[0] == 2 { //SNMPv1
                        resp.Version = "3"
                }

        }
        return resp

}

func serveSNMP() {
        ServerAddr, err := net.ResolveUDPAddr("udp", ":162")
        checkError(err)
        ServerConn, err := net.ListenUDP("udp", ServerAddr)
        checkError(err)
        defer ServerConn.Close()
        buf := make([]byte, 2048)
        for {
                n, addr, err := ServerConn.ReadFromUDP(buf)
                checkError(err)
                //fmt.Println(snmpParse(buf[0:n]))
                //              fmt.Println("Received from:", addr.IP.String())
                pp := snmpParse(buf[0:n])
                if pp.Version == "v2c" && pp.Variables[1].Name == ".1.3.6.1.6.3.1.1.4.1.0" && (pp.Variables[1].Value == snmp_linkDown || pp.Variables[1].Value == snmp_linkUp) {
                        //fmt.Print("Received from:", addr.IP.String()+"_"+strconv.Itoa(pp.Variables[2].Value.(int)), "\t")
                        mutex.Lock()
                        ma_ud[addr.IP.String()+"_"+strconv.Itoa(pp.Variables[2].Value.(int))] += 1
                        if ma_ud[addr.IP.String()+"_"+strconv.Itoa(pp.Variables[2].Value.(int))] > 1440 {
                                ma_ud[addr.IP.String()+"_"+strconv.Itoa(pp.Variables[2].Value.(int))] -= 1
                        }
                        ma_com[addr.IP.String()] = pp.Community
                        mutex.Unlock()
                        //                      fmt.Println(ma)
                }
                //              fmt.Println(pp.Variables[1])
        }
        //      packet := []byte{48, 130, 0, 119, 2, 1, 1, 4, 4, 122, 116, 114, 119, 167, 130, 0, 106, 2, 3, 1, 8, 22, 2, 1, 0, 2, 1, 0, 48, 130, 0, 91, 48, 16, 6, 8, 43, 6, 1, 2, 1, 1, 3, 0, 67, 4, 6, 171, 37, 62, 48, 28, 6, 10, 43, 6, 1, 6, 3, 1, 1, 4, 1, 0, 6, 14, 43, 6, 1, 4, 1, 129, 43, 11, 64, 1, 2, 15, 0, 3, 48, 41, 6, 13, 43, 6, 1, 4, 1, 129, 43, 11, 64, 1, 2, 15, 1, 4, 24, 2, 16, 39, 190, 3, 29, 149, 0, 1, 0, 9, 0, 1, 16, 39, 190, 3, 29, 149, 0, 1, 0, 9, 0}
}

func handler(w http.ResponseWriter, r *http.Request) {
        fmt.Fprintf(w, "<html><head></head><body><a href=/flap>Flap</a><br><a href=/com>Community</a></body></html>")
}

func handler_com(w http.ResponseWriter, r *http.Request) {
        fmt.Fprintf(w, "<html><head></head><body><h1>Таблица Community</h1><table border=1>")
        mutex.Lock()
        for k, v := range ma_com {
                fmt.Fprintf(w, "<tr><td><a href=http://217.107.196.60:81/checkIfaces/%s>%s</a></td><td>%s</td></tr>\n", k, k, v)

        }
        mutex.Unlock()
        fmt.Fprintf(w, "</table></body></html>")

}

func handler_flap(w http.ResponseWriter, r *http.Request) {
        fmt.Fprintf(w, "<html><head></head><body><h1>Топ Флапающий портов</h1><table border=1>")
        n := map[int][]string{}
        var a []int
        mutex.Lock()
        for k, v := range ma_ud {
                n[v] = append(n[v], k)
        }
        mutex.Unlock()
        for k := range n {
                a = append(a, k)
        }
        sort.Sort(sort.Reverse(sort.IntSlice(a)))
        fmt.Fprintf(w, "<th>Количество переключений</th><th>IP адрес комутатора</th><th>Порт</th>")
        for _, k := range a {
                for _, s := range n[k] {
                        if k > 5 {
                                fmt.Fprintf(w, "<tr><td>%d</td><td><a href=http://217.107.196.60:81/checkIfaces/%s>%s</a></td></tr>\n", k, strings.Split(s, "_")[0], strings.Replace(s, "_", "</td><td>", 1))
                        }
                }
        }
        //    for key, value := range foxSort(ma) {
        //      fmt.Fprintf(w,"<tr><td>"+key+"</td><td>"+strconv.Itoa(value)+"</td></tr>\n")
        //      fmt.Println(key,value)
        //    }
        fmt.Fprintf(w, "</table></body></html>")
}

func clearOLD(sec time.Duration) {
        for {
                time.Sleep(sec * 1000000000)
                mutex.Lock()
                for k, _ := range ma_ud {
                        ma_ud[k] -= 1
                        if ma_ud[k] < 1 {
                                delete(ma_ud, k)
                        }
                }
                mutex.Unlock()
        }

}

var ma_ud map[string]int
var ma_com map[string]string
var mutex sync.Mutex

func main() {
        ma_ud = make(map[string]int)
        ma_com = make(map[string]string)
        mutex = sync.Mutex{}
        http.HandleFunc("/", handler)
        http.HandleFunc("/flap", handler_flap)
        http.HandleFunc("/com", handler_com)
        go http.ListenAndServe(":85", nil)
        go clearOLD(60)
        serveSNMP()
}
