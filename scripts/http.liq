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
      # TODO: make sure that content-length is not already fixed..
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

# Enable HTTP json-rpc handling on the given path.
# @category Interaction
# @param path Path to receive JSON-RPC requests.
# @param ~headers Additional headers to add to the response, e.g. ["Access-Control-Allow-Origin","*"]
# @param ~mime Content-types for JSON data.
def harbor.http.json_rpc(~headers=[],~mime=["application/json"], path) =
  # TODO: make sure that Content-Type is not already set..
  headers = list.append([("Content-Type","application/json")], headers)
  def json_rpc(request) =
    # TODO: there is something fishy here..
    request_headers = request.headers
    # TODO: match also lower case..
    content_type = request_headers["Content-Type"] 
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
  harbor.http.register(port=8005,path,json_rpc)
end
