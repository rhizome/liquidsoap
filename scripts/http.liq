# Set of HTTP utils.

%include "http_codes.liq"

# Create a HTTP response callback when a data callback is provided.
# @category Interaction
# @param response Record containing all required informations.
def http.response(response) =
  code        = ?(response.code=200)
  headers     = ?(response.headers=[])
  protocol    = ?(response.protocol="HTTP/1.0")
  static_data = ?(response.data.static="")
  stream_data = ?(response.data.stream={""})  

  codes  = http.codes
  status = codes[string_of(code)]
  headers = 
    if not ?response.data.stream then
      list.append([("Content-Length",
                    "#{string.length(static_data)}")],
                  headers)
    else
      headers
    end
  headers = list.map(fun (x) -> "#{fst(x)}: #{snd(x)}",headers)
  headers = string.concat(separator="\r\n",headers)
  # If no headers are provided, we should avoid
  # having an empty line for them. Therefore, we also
  # conditionally add the final \r\n here.
  headers =
    if headers != "" then
      "#{headers}\r\n"
    else
      headers
    end
  headers_sent = ref false
  def callback () = 
    if not !headers_sent then
      headers_sent := true
      "#{protocol} #{code} #{status}\r\n\
      #{headers}\
      \r\n#{static_data}"
    else
      stream_data()
    end
  end
  callback
end

%ifdef json.rpc
# Enable HTTP json-rpc handling on the given path.
# @category Interaction
# @param path Path to receive JSON-RPC requests.
# @param ~port Port where JSON-RPC requests should be adressed.
# @param ~headers Additional headers to add to the response, e.g. ["Access-Control-Allow-Origin","*"]
# @param ~mime Content-types for JSON data.
def http.harbor.json_rpc(~port,path,~headers=[],~mime=["application/json"]) =
  # JSON canonical mime is always the first element passed in "mime" list
  canonical_mime = 
    if list.length(mime) > 0 then
      list.hd(mime)
    else
      "application/json"
  end

  # Add content-type is not already done
  # A copy of headers with labels all in lowercase.
  low_headers = list.map(fun (x) -> (string.case(fst(x)), snd(x)), headers)
  headers = 
    if list.mem_assoc("content-type", low_headers) then
      headers
    else
      list.append([("Content-Type",canonical_mime)], headers)
  end

  def json_rpc(request) =
    low_req_headers = list.map(fun (x) -> (string.case(fst(x)), snd(x)), request.headers)
    content_type = low_req_headers["content-type"] 
    response =
      [protocol = request.protocol,
       code     = 405,
       headers  = headers]
    if request.method != "POST" then
      http.response(
        [response with 
          data=[static="JSON-RPC requests should be performed using a POST request"]])
    elsif not list.mem(content_type, mime) then
      http.response(
        [response with
          data=[static="Invalid content-type."]])
    else
      http.response(
        [response with
           code=200,
           data=[static=json.rpc.execute(request.data)]])
    end
  end
  http.harbor.register(port=port, path, json_rpc)
end
%endif
