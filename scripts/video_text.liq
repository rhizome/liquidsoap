%ifdef video.gd.add_text
# Add a scrolling line of text on video frames.
# @category Source / Video Processing
# @param ~id       Force the value of the source ID.
# @param ~color    Text color (in 0xRRGGBB format).
# @param ~cycle    Cycle text.
# @param ~font     Path to ttf font file.
# @param ~metadata Change text on a particular metadata \
#                  (empty string means disabled).
# @param ~size     Font size.
# @param ~speed    Speed in pixels per second (0 means no scrolling).
# @param ~x        x offset (negative means from right).
# @param ~y        y offset (negative means from bottom).
# @param text      Text to display.
def video.add_text(~id="",~color=16777215,~cycle=true,
                   ~font=configure.default_font,
                   ~metadata="",~size=18,~speed=70,~x=-1,~y=-5,
                   text,source)
  video.add_text.gd(id=id,color=color,cycle=cycle,font=font,metadata=metadata,
                    size=size,speed=speed,x=x,y=y,text,source)
end
%endif

%ifdef video.sdl.add_text
# Add a scrolling line of text on video frames.
# @category Source / Video Processing
# @param ~id       Force the value of the source ID.
# @param ~color    Text color (in 0xRRGGBB format).
# @param ~cycle    Cycle text.
# @param ~font     Path to ttf font file.
# @param ~metadata Change text on a particular metadata \
#                  (empty string means disabled).
# @param ~size     Font size.
# @param ~speed    Speed in pixels per second (0 means no scrolling).
# @param ~x        x offset (negative means from right).
# @param ~y        y offset (negative means from bottom).
# @param text      Text to display.
def video.add_text(~id="",~color=16777215,~cycle=true,
                   ~font=configure.default_font,
                   ~metadata="",~size=18,~speed=70,~x=-1,~y=-5,
                   text,source)
  video.sdl.add_text(id=id,color=color,cycle=cycle,font=font,metadata=metadata,
                     size=size,speed=speed,x=x,y=y,text,source)
end
%endif