class MessageSendStruct
{
    int msgid;
    Clock clock;
    MessageSendStruct(int mid, Clock nwclock)
    {
        msgid=mid;
        clock=nwclock;
    }
    int getMsgid(){return msgid;}
    Clock getMsgClock(){return clock;}
}