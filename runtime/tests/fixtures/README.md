The HTTP localhost certificate and PKCS#8 key are intentionally public test
fixtures, generated with OpenSSL for CN/SAN localhost. They must never be used
outside tests. Native HTTP tests run a loopback TLS server and check both a
specifically trusted certificate and rejection by the default system verifier.
They do not modify the machine's trust store or contact the public network.
