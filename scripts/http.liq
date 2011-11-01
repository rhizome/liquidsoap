# Set of HTTP utils.

%include "http_codes.liq"

http_response_base = 
  [protocol="HTTP/1.1",
   code=200,
   headers=[]]

# Create a HTTP response callback when a data callback is provided.
# @category Interaction
# @param response Record containing all required informations.
def http_response(response) =
  status = http_codes[string_of(response.code)]
  headers = list.map(fun (x) -> "#{fst(x)}: #{snd(x)}",response.headers)
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
      "#{response.protocol} #{response.code} #{status}\r\n\
      #{headers}\
      \r\n"
    else
      response.data()
    end
  end
  callback
end

# Create a HTTP response callback with a simple response string.
# @category Interaction
# @param response Record containing all required informations.
def http_simple_response(response) =
  status = http_codes[string_of(response.code)]
  # Set content-length if needed and not set by the
  # user.
  headers =
    if response.data != "" and
       not list.mem_assoc("Content-Length",response.headers)
    then
      list.append([("Content-Length",
                    "#{string.length(response.data)}")],
                  response.headers)
    else
      response.headers
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
  data_sent    = ref false
  def callback () =
    if not !headers_sent then
      headers_sent := true
      "#{response.protocol} #{response.code} #{status}\r\n\
      #{headers}\
      \r\n"
    else
      if !data_sent then
        ""
      else
        data_sent := true
        response.data
      end
    end
  end
  callback
end
