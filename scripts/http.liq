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
    if not response.data.stream? then
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
